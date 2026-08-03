//! Closure/application machinery: lambdas, calls, variable references, and
//! per-type specialization.

use crate::ast::*;
use crate::types::{Monotype, TypeFunc};
use melior::dialect::{arith, func, llvm, scf};
use melior::ir::{
    Attribute,
    attribute::{
        BoolAttribute, DenseI32ArrayAttribute, FlatSymbolRefAttribute, FloatAttribute,
        IntegerAttribute, StringAttribute, TypeAttribute,
    },
    operation::OperationBuilder,
    r#type::{FunctionType, IntegerType},
    Block, BlockLike, Identifier, Location, Region, RegionLike, Type, Value, ValueLike,
};
use std::collections::HashMap;

use super::{AbstractionInfo, Env, EnvEntry, Module};
use super::closures::{build_closure, closure_call, env_struct_type, free_variables, load_field};
use super::enums::{build_enum_value, build_payload};
use super::expr::lower_expr;
use super::lists::empty_list;
use super::types::lower_type;

pub(crate) fn lower_let<'c, 'a>(
    name: &str,
    e1: &Expr,
    e2: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    if let Some(value) = lower_tail_recursive_let(name, e1, e2, block, module, env)? {
        return Ok(value);
    }
    let previous = env.get(name).cloned();
    bind_in_env(name, e1, block, module, env)?;
    let result = lower_expr(e2, block, module, env);
    match previous {
        Some(old) => {
            env.insert(name.to_string(), old);
        }
        None => {
            env.remove(name);
        }
    }
    result
}

/// Lower the common tail-recursive closure shape using nested `scf.while`
/// regions. Captures from the surrounding scope (such as `n` in `tl_fib`)
/// remain ordinary SSA values visible to both regions.
fn lower_tail_recursive_let<'c, 'a>(
    name: &str,
    function: &Expr,
    continuation: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Option<Value<'c, 'a>>, String> {
    let (params, body) = peel_abstractions(function);
    if params.len() != 3 {
        return Ok(None);
    }
    let ENode::IfElse(condition, then_branch, else_branch) = &*body.e else {
        return Ok(None);
    };
    let ENode::Variable(then_name) = &*then_branch.e else {
        return Ok(None);
    };
    if then_name != &params[1].0 {
        return Ok(None);
    }
    let (callee, next_args) = flatten_application(else_branch);
    if callee != name || next_args.len() != 3 {
        return Ok(None);
    }
    let (initial_callee, initial_args) = flatten_application(continuation);
    if initial_callee != name || initial_args.len() != 3 {
        return Ok(None);
    }

    let initial: Vec<Value<'c, 'a>> = initial_args
        .iter()
        .map(|arg| lower_expr(arg, block, module, env))
        .collect::<Result<_, _>>()?;
    let types: Vec<Type<'c>> = initial.iter().map(|value| value.r#type()).collect();
    let location = Location::unknown(module.context);

    let before_block = Block::new(&types.iter().map(|typ| (*typ, location)).collect::<Vec<_>>());
    let before_values: Vec<Value<'c, '_>> = (0..3)
        .map(|index| before_block.argument(index).map(Into::into).map_err(|e| e.to_string()))
        .collect::<Result<_, _>>()?;
    let mut before_env = env.clone();
    for (index, (param, _)) in params.iter().enumerate() {
        before_env.insert(param.clone(), EnvEntry::Value(before_values[index]));
    }
    let cond = match &*condition.e {
        ENode::Comparison(CompOp::Eq, lhs, rhs) => {
            let lhs = lower_expr(lhs, &before_block, module, &mut before_env)?;
            let rhs = lower_expr(rhs, &before_block, module, &mut before_env)?;
            before_block
                .append_operation(arith::cmpi(
                    module.context,
                    arith::CmpiPredicate::Ne,
                    lhs,
                    rhs,
                    location,
                ))
                .result(0)
                .map_err(|e| e.to_string())?
                .into()
        }
        _ => return Ok(None),
    };
    before_block.append_operation(scf::condition(cond, &before_values, location));
    let before_region = Region::new();
    before_region.append_block(before_block);

    let after_block = Block::new(&types.iter().map(|typ| (*typ, location)).collect::<Vec<_>>());
    let after_values: Vec<Value<'c, '_>> = (0..3)
        .map(|index| after_block.argument(index).map(Into::into).map_err(|e| e.to_string()))
        .collect::<Result<_, _>>()?;
    let mut after_env = env.clone();
    for (index, (param, _)) in params.iter().enumerate() {
        after_env.insert(param.clone(), EnvEntry::Value(after_values[index]));
    }
    let next_values: Vec<Value<'c, '_>> = next_args
        .iter()
        .map(|arg| lower_expr(arg, &after_block, module, &mut after_env))
        .collect::<Result<_, _>>()?;
    after_block.append_operation(scf::r#yield(&next_values, location));
    let after_region = Region::new();
    after_region.append_block(after_block);

    let while_op = scf::r#while(&initial, &types, before_region, after_region, location);
    let while_value = block.append_operation(while_op).result(1).map_err(|e| e.to_string())?;
    Ok(Some(while_value.into()))
}

fn peel_abstractions(expr: &Expr) -> (Vec<(String, crate::ast::Type)>, Expr) {
    let mut params = Vec::new();
    let mut current = expr.clone();
    loop {
        match *current.e {
            ENode::Abstraction(binding, body) => {
                params.push((binding.0.clone(), (*binding.1).clone()));
                current = *body;
            }
            _ => return (params, current),
        }
    }
}

fn flatten_application(expr: &Expr) -> (&str, Vec<Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        match &*current.e {
            ENode::Application(f, arg) => {
                args.push((**arg).clone());
                current = f;
            }
            ENode::Variable(name) => {
                args.reverse();
                return (name, args);
            }
            _ => return ("", Vec::new()),
        }
    }
}

/// Bind `name` to the lowered value of `e2` in `env`.
///
/// A lambda initializer is registered in [`Module::abstractions`] (bound as
/// an [`EnvEntry::Abstraction`]) so it stays polymorphic and is specialized on
/// demand at each use of `name`.
pub(crate) fn bind_in_env<'c, 'a>(
    name: &str,
    e2: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<(), String> {
    if let ENode::Abstraction(binding, body) = &*e2.e {
        let sym = format!("let_{}", module.let_counter);
        module.let_counter += 1;
        module.abstractions.insert(
            sym.clone(),
            AbstractionInfo {
                param: binding.0.clone(),
                param_type: binding.1.t.clone(),
                body: (**body).clone(),
                abs_type: e2.typ.clone(),
            },
        );
        env.insert(name.to_string(), EnvEntry::Abstraction(sym));
    } else {
        let value = lower_expr(e2, block, module, env)?;
        env.insert(name.to_string(), EnvEntry::Value(value));
    }
    Ok(())
}

/// Emit a `func.constant` reference to the specialization of `sym` at the
/// concrete type `typ`, returning a func-typed SSA value.
fn reference_specialization<'c, 'a>(
    sym: &str,
    self_name: &str,
    typ: &Monotype,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
) -> Result<Value<'c, 'a>, String> {
    let symbol = specialize_binding(sym, self_name, typ, module)?;
    let (param_mono, ret_mono) = concrete_parts(typ)
        .ok_or_else(|| format!("codegen: cannot reference `{sym}`: not a function type"))?;
    let func_type = FunctionType::new(
        module.context,
        &[lower_type(&param_mono, module)?],
        &[lower_type(&ret_mono, module)?],
    );
    let location = Location::unknown(module.context);
    block
        .append_operation(func::constant(
            module.context,
            FlatSymbolRefAttribute::new(module.context, &symbol),
            func_type,
            location,
        ))
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Lower a variable reference: a bound value/abstraction if it is in `env`, a
/// specialized closure if it names a registered lambda binding, otherwise a
/// `func.call` on the top-level symbol of the same name.
pub(crate) fn lower_variable<'c, 'a>(
    expr: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let ENode::Variable(name) = &*expr.e else {
        unreachable!()
    };
    match env.get(name) {
        Some(EnvEntry::Value(value)) => return Ok(*value),
        Some(EnvEntry::Abstraction(sym)) => {
            return reference_specialization(sym, name, &expr.typ, block, module);
        }
        None => {}
    }

    // A top-level lambda binding is specialized at the concrete type this use
    // site resolved to, and referenced by `func.constant` on that
    // specialization.
    if module.abstractions.contains_key(name) {
        return reference_specialization(name, name, &expr.typ, block, module);
    }

    // A nullary enum constructor (`None`) builds a tagged value with no
    // payload.
    if let Some(&(_, variant_index, arity)) = module.constructors.get(name) {
        if arity == 0 {
            let location = Location::unknown(module.context);
            let payload = empty_list(block, module)?;
            return build_enum_value(module, block, variant_index, payload, location);
        }
    }

    let function_type = module.symbols.get(name).ok_or_else(|| {
        format!("codegen: undefined variable `{name}` (not a bound parameter or symbol)")
    })?;

    let location = Location::unknown(module.context);
    let mut results = Vec::new();
    for i in 0..function_type.result_count() {
        results.push(function_type.result(i).map_err(|e| e.to_string())?);
    }
    let call = func::call(
        module.context,
        FlatSymbolRefAttribute::new(module.context, name),
        &[],
        &results,
        location,
    );
    block
        .append_operation(call)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Emit (or reuse) a `func.func` for `name` specialized at the concrete
/// function type `typ`, returning its symbol.
///
/// The compiled function takes `(param, env)` — every function accepts an
/// environment pointer (a closure) so calls are uniform. The specialization is
/// cached by `(name, typ)` so each instantiation is emitted exactly once; the
/// cache is populated *before* the body is lowered so recursive uses of `name`
/// at the same type resolve to the in-progress symbol.
fn specialize_binding<'c>(
    name: &str,
    self_name: &str,
    typ: &Monotype,
    module: &mut Module<'c>,
) -> Result<String, String> {
    let (param_mono, ret_mono) = concrete_parts(typ)
        .ok_or_else(|| format!("codegen: cannot specialize `{name}`: not a single-argument function type"))?;

    let key = (name.to_string(), format!("{param_mono:?}->{ret_mono:?}"));
    if let Some(symbol) = module.specializations.get(&key) {
        return Ok(symbol.clone());
    }

    let info = module.abstractions.get(name).ok_or_else(|| {
        format!("codegen: `{name}` is not a registered lambda binding")
    })?;
    let param = info.param.clone();
    let mut body = info.body.clone();

    // The definition statement may leave the body's types partially abstract
    // (e.g. a recursive call whose result type is unconstrained there); unify
    // the abstraction's resolved type with this instantiation to get concrete
    // types for the specialization.
    let substitution = crate::types::unify(&info.abs_type, typ)
        .map_err(|e| format!("codegen: cannot specialize `{name}`: {}", e.message))?;
    crate::ast::apply_substitution(&mut body, &substitution);

    let symbol = format!("{name}_spec_{}", module.spec_counter);
    module.spec_counter += 1;
    module.specializations.insert(key, symbol.clone());

    let param_mlir = lower_type(&param_mono, module)?;
    let ret_mlir = lower_type(&ret_mono, module)?;
    let location = Location::unknown(module.context);

    let closure_block = Block::new(&[(param_mlir, location)]);
    let arg = closure_block.argument(0).map_err(|e| e.to_string())?;
    let mut env = HashMap::new();
    env.insert(param, EnvEntry::Value(arg.into()));
    if self_name != name {
        env.insert(self_name.to_string(), EnvEntry::Abstraction(name.to_string()));
    }

    let body_value = lower_expr(&body, &closure_block, module, &mut env)?;
    closure_block.append_operation(func::r#return(&[body_value], location));

    let function_type =
        FunctionType::new(module.context, &[param_mlir], &[ret_mlir]);
    let region = Region::new();
    region.append_block(closure_block);

    let function = func::func(
        module.context,
        StringAttribute::new(module.context, &symbol),
        TypeAttribute::new(function_type.into()),
        region,
        &[],
        location,
    );
    module.module.body().append_operation(function);
    module.functions += 1;

    Ok(symbol)
}

/// Lower a function application `f x` by calling the closure `f`, or — when
/// `f` is an enum constructor — by building the tagged value.
///
/// The function's resolved type must be a single-argument function type
/// `A => B`.
pub(crate) fn lower_application<'c, 'a>(
    f: &Expr,
    x: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let location = Location::unknown(module.context);

    if let ENode::Variable(name) = &*f.e {
        if let Some(&(_, variant_index, arity)) = module.constructors.get(name) {
            if arity != 1 {
                return Err(format!(
                    "codegen: constructor `{name}` applied to the wrong number of arguments"
                ));
            }
            let value = lower_expr(x, block, module, env)?;
            let typ = lower_type(&default_free_vars(&x.typ), module)?;
            let payload = build_payload(module, block, &[(value, typ)], location)?;
            return build_enum_value(module, block, variant_index, payload, location);
        }

        let sym = if module.abstractions.contains_key(name) {
            Some(name.clone())
        } else if let Some(EnvEntry::Abstraction(s)) = env.get(name) {
            Some(s.clone())
        } else {
            None
        };

        if let Some(sym) = sym {
            if let Some(info) = module.abstractions.get(&sym) {
                let param = info.param.clone();
                let mut body = info.body.clone();
                let mut applied_typ = info.abs_type.clone();

                let substitution = crate::types::unify(&info.abs_type, &default_free_vars(&f.typ))
                    .map_err(|e| format!("codegen: cannot specialize `{}`: {}", name, e.message))?;
                crate::ast::apply_substitution(&mut body, &substitution);
                applied_typ = applied_typ.apply(&substitution);

                let (param_mono, ret_mono) = concrete_parts(&applied_typ).ok_or_else(|| {
                    format!("codegen: cannot apply `{}`: not a function type", name)
                })?;

                if is_scalar_type(&ret_mono) {
                    if has_self_reference(&body, name) {
                        drop(body);
                        let symbol = specialize_binding(&sym, name, &default_free_vars(&f.typ), module)?;
                        let func_type = FunctionType::new(
                            module.context,
                            &[lower_type(&param_mono, module)?],
                            &[lower_type(&ret_mono, module)?],
                        );
                        let fn_val = block
                            .append_operation(func::constant(
                                module.context,
                                FlatSymbolRefAttribute::new(module.context, &symbol),
                                func_type,
                                location,
                            ))
                            .result(0)
                            .map_err(|e| e.to_string())?;
                        let arg_value = lower_expr(x, block, module, env)?;
                        return block
                            .append_operation(func::call_indirect(
                                fn_val.into(),
                                &[arg_value],
                                &[lower_type(&ret_mono, module)?],
                                location,
                            ))
                            .result(0)
                            .map_err(|e| e.to_string())
                            .map(Into::into);
                    }

                    let body = substitute_variable(body, &param, x);
                    let arg_value = lower_expr(x, block, module, env)?;
                    let prev = env.insert(param.clone(), EnvEntry::Value(arg_value));
                    let result = lower_expr(&body, block, module, env);
                    match prev {
                        Some(v) => { env.insert(param, v); }
                        None => { env.remove(&param); }
                    }
                    return result;
                }

                let body = substitute_variable(body, &param, x);
                let (inner_param, inner_body) = match *body.e {
                    ENode::Abstraction(binding, b) => (binding.0.clone(), *b),
                    _ => {
                        return Err(format!(
                            "codegen: partial application of `{}` body is not a lambda",
                            name
                        ));
                    }
                };

                let (inner_param_mono, _) = concrete_parts(&ret_mono).ok_or_else(|| {
                    format!("codegen: partial application of `{}` has non-function return", name)
                })?;
                let (_, final_ret_mono) = concrete_parts(&ret_mono).ok_or_else(|| {
                    format!("codegen: partial application `{}` inner function has invalid type", name)
                })?;
                let param_mlir = lower_type(&inner_param_mono, module)?;
                let ret_mlir = lower_type(&final_ret_mono, module)?;
                let function_type =
                    FunctionType::new(module.context, &[param_mlir], &[ret_mlir]);

                // Cache partial applications by (binding, argument, type) so a
                // recursive partial application (e.g. `map fn xs` inside the
                // body of `map`) reuses the emitted function instead of
                // re-lowering infinitely.
                let cache_key = (sym.clone(), expr_key(x), format!("{:?}", applied_typ));
                if let Some(symbol) = module.partials.get(&cache_key) {
                    let symbol = symbol.clone();
                    return block
                        .append_operation(func::constant(
                            module.context,
                            FlatSymbolRefAttribute::new(module.context, &symbol),
                            function_type,
                            location,
                        ))
                        .result(0)
                        .map_err(|e| e.to_string())
                        .map(Into::into);
                }

                let symbol = format!("{name}_partial_{}", module.spec_counter);
                module.spec_counter += 1;
                module.partials.insert(cache_key, symbol.clone());

                let closure_block = Block::new(&[(param_mlir, location)]);
                let arg: Value<'c, 'a> = closure_block.argument(0).map_err(|e| e.to_string())?.into();
                let mut closure_env = HashMap::new();
                closure_env.insert(inner_param, EnvEntry::Value(arg));

                let free = free_variables(&inner_body);
                for (capture, entry) in env.iter() {
                    if free.contains(capture) {
                        match entry {
                            EnvEntry::Value(v) => {
                                closure_env.insert(capture.clone(), EnvEntry::Value(*v));
                            }
                            EnvEntry::Abstraction(sym) => {
                                closure_env.insert(capture.clone(), EnvEntry::Abstraction(sym.clone()));
                            }
                        }
                    }
                }

                let body_value = lower_expr(&inner_body, &closure_block, module, &mut closure_env)?;
                closure_block.append_operation(func::r#return(&[body_value], location));

                let region = Region::new();
                region.append_block(closure_block);

                let function = func::func(
                    module.context,
                    StringAttribute::new(module.context, &symbol),
                    TypeAttribute::new(function_type.into()),
                    region,
                    &[],
                    location,
                );
                module.module.body().append_operation(function);
                module.functions += 1;

                return block
                    .append_operation(func::constant(
                        module.context,
                        FlatSymbolRefAttribute::new(module.context, &symbol),
                        function_type,
                        location,
                    ))
                    .result(0)
                    .map_err(|e| e.to_string())
                    .map(Into::into);
            }
        }
    }

    let function = lower_expr(f, block, module, env)?;
    let argument = lower_expr(x, block, module, env)?;

    let func_type_str = function.r#type().to_string();
    if func_type_str.starts_with("(") {
        let func_type = FunctionType::try_from(function.r#type())
            .map_err(|_| "codegen: expected function type for call_indirect".to_string())?;
        let mut ret_types = Vec::with_capacity(func_type.result_count());
        for i in 0..func_type.result_count() {
            ret_types.push(func_type.result(i).map_err(|e| e.to_string())?);
        }
        block
            .append_operation(func::call_indirect(
                function,
                &[argument],
                &ret_types,
                location,
            ))
            .result(0)
            .map_err(|e| e.to_string())
            .map(Into::into)
    } else {
        let (_, ret_mono) = concrete_parts(&f.typ).ok_or_else(|| {
            format!(
                "codegen: cannot apply {:?}: expected a single-argument function type",
                *f.e
            )
        })?;
        let ret_mlir = lower_type(&ret_mono, module)?;
        closure_call(module, block, function, &[argument], ret_mlir, location)
    }
}

/// Split a single-argument function type `A => B` into `(A, B)`.
fn function_parts(typ: &Monotype) -> Option<(Monotype, Monotype)> {
    match typ {
        Monotype::TypeFuncApplication(f, args)
            if matches!(**f, TypeFunc::Fn) && args.len() == 2 =>
        {
            Some((args[0].clone(), args[1].clone()))
        }
        _ => None,
    }
}

/// Replace any remaining type variables with `int`, monomorphizing types the
/// type checker left unconstrained (e.g. the discarded result of applying a
/// polymorphic function). MLIR needs a concrete type, and a free variable has
/// no other constraint to satisfy.
pub(crate) fn default_free_vars(typ: &Monotype) -> Monotype {
    match typ {
        Monotype::TypeVariable(_) => Monotype::int(),
        Monotype::TypeFuncApplication(f, args) => Monotype::TypeFuncApplication(
            f.clone(),
            args.iter().map(default_free_vars).collect(),
        ),
    }
}

/// [`function_parts`] with free type variables defaulted to `int`.
fn concrete_parts(typ: &Monotype) -> Option<(Monotype, Monotype)> {
    function_parts(typ).map(|(a, b)| (default_free_vars(&a), default_free_vars(&b)))
}

fn is_scalar_type(typ: &Monotype) -> bool {
    !matches!(typ, Monotype::TypeFuncApplication(f, _) if matches!(**f, TypeFunc::Fn))
}

/// A compact, stable fingerprint of an expression, used to key partial
/// applications. Two syntactically identical expressions produce the same key.
fn expr_key(e: &Expr) -> String {
    match &*e.e {
        ENode::Variable(n) => format!("v:{n}"),
        ENode::Literal(l) => format!("l:{l:?}"),
        ENode::Abstraction(b, body) => format!("a:{}:{}", b.0, expr_key(body)),
        ENode::Application(f, x) => format!("({} {})", expr_key(f), expr_key(x)),
        ENode::Let(n, e1, e2) => format!("let{n}={} in {}", expr_key(e1), expr_key(e2)),
        ENode::IfElse(c, t, e) => format!(
            "if{}then{}else{}",
            expr_key(c),
            expr_key(t),
            expr_key(e)
        ),
        ENode::Block(stmts, e) => format!("blk{}{}", stmts.len(), expr_key(e)),
        ENode::Comparison(o, a, b) => format!("c{o:?}{}{}", expr_key(a), expr_key(b)),
        ENode::Arithmetic(o, a, b) => format!("a{o:?}{}{}", expr_key(a), expr_key(b)),
        ENode::Logical(o, a, b) => format!("l{o:?}{}{}", expr_key(a), expr_key(b)),
        ENode::Unary(o, e) => format!("u{o:?}{}", expr_key(e)),
        ENode::List(es) => format!(
            "[{}]",
            es.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        ENode::Cons(h, t) => format!("{}::{}", expr_key(h), expr_key(t)),
        ENode::Match(s, cases) => format!("m{}{}", expr_key(s), cases.len()),
    }
}

fn has_self_reference(expr: &Expr, name: &str) -> bool {
    match &*expr.e {
        ENode::Variable(n) => n == name,
        ENode::Literal(_) => false,
        ENode::Abstraction(binding, body) => {
            if binding.0 == name {
                false
            } else {
                has_self_reference(body, name)
            }
        }
        ENode::Application(f, x) => has_self_reference(f, name) || has_self_reference(x, name),
        ENode::Let(n, e1, e2) => {
            if n == name { false }
            else { has_self_reference(e1, name) || has_self_reference(e2, name) }
        }
        ENode::IfElse(c, t, e) => has_self_reference(c, name) || has_self_reference(t, name) || has_self_reference(e, name),
        ENode::Block(stmts, e) => {
            stmts.iter().any(|s| has_self_reference_stmt(s, name)) || has_self_reference(e, name)
        }
        ENode::Comparison(_, a, b) | ENode::Arithmetic(_, a, b) | ENode::Logical(_, a, b) => {
            has_self_reference(a, name) || has_self_reference(b, name)
        }
        ENode::Unary(_, e) => has_self_reference(e, name),
        ENode::List(es) => es.iter().any(|e| has_self_reference(e, name)),
        ENode::Cons(h, t) => has_self_reference(h, name) || has_self_reference(t, name),
        ENode::Match(scrut, cases) => {
            has_self_reference(scrut, name)
                || cases.iter().any(|c| has_self_reference(&c.val, name) || has_self_reference(&c.exp, name))
        }
    }
}

fn has_self_reference_stmt(stmt: &Stmt, name: &str) -> bool {
    match &*stmt.s {
        SNode::Decl(e1, _, e2) => has_self_reference(e1, name) || has_self_reference(e2, name),
        SNode::Expr(e1) => has_self_reference(e1, name),
        SNode::Print(e1) => has_self_reference(e1, name),
        SNode::TypeDecl(..) => false,
    }
}

fn substitute_variable(expr: Expr, name: &str, replacement: &Expr) -> Expr {
    let new_e: ENode = match *expr.e {
        ENode::Variable(ref n) if n == name => (*replacement.e).clone(),
        ENode::Variable(_) => *expr.e,
        ENode::Literal(_) => *expr.e,
        ENode::Abstraction(binding, body) => {
            let Binding(param, ptype) = *binding;
            if param == name {
                ENode::Abstraction(Box::new(Binding(param.clone(), ptype)), body)
            } else {
                ENode::Abstraction(
                    Box::new(Binding(param, ptype)),
                    Box::new(substitute_variable(*body, name, replacement)),
                )
            }
        }
        ENode::Application(f, arg) => ENode::Application(
            Box::new(substitute_variable(*f, name, replacement)),
            Box::new(substitute_variable(*arg, name, replacement)),
        ),
        ENode::Let(n, e1, e2) => {
            if n == name {
                ENode::Let(n, e1, e2)
            } else {
                ENode::Let(
                    n,
                    Box::new(substitute_variable(*e1, name, replacement)),
                    Box::new(substitute_variable(*e2, name, replacement)),
                )
            }
        }
        ENode::IfElse(c, t, e) => ENode::IfElse(
            Box::new(substitute_variable(*c, name, replacement)),
            Box::new(substitute_variable(*t, name, replacement)),
            Box::new(substitute_variable(*e, name, replacement)),
        ),
        ENode::Block(stmts, e) => ENode::Block(
            stmts.into_iter().map(|s| substitute_stmt(s, name, replacement)).collect(),
            Box::new(substitute_variable(*e, name, replacement)),
        ),
        ENode::Comparison(op, a, b) => ENode::Comparison(
            op,
            Box::new(substitute_variable(*a, name, replacement)),
            Box::new(substitute_variable(*b, name, replacement)),
        ),
        ENode::Arithmetic(op, a, b) => ENode::Arithmetic(
            op,
            Box::new(substitute_variable(*a, name, replacement)),
            Box::new(substitute_variable(*b, name, replacement)),
        ),
        ENode::Logical(op, a, b) => ENode::Logical(
            op,
            Box::new(substitute_variable(*a, name, replacement)),
            Box::new(substitute_variable(*b, name, replacement)),
        ),
        ENode::Unary(op, e) => ENode::Unary(
            op,
            Box::new(substitute_variable(*e, name, replacement)),
        ),
        ENode::List(es) => ENode::List(
            es.into_iter().map(|e| substitute_variable(e, name, replacement)).collect(),
        ),
        ENode::Cons(h, t) => ENode::Cons(
            Box::new(substitute_variable(*h, name, replacement)),
            Box::new(substitute_variable(*t, name, replacement)),
        ),
        ENode::Match(scrut, cases) => ENode::Match(
            Box::new(substitute_variable(*scrut, name, replacement)),
            cases.into_iter().map(|c| MatchCase {
                val: Box::new(substitute_variable(*c.val, name, replacement)),
                exp: Box::new(substitute_variable(*c.exp, name, replacement)),
            }).collect(),
        ),
    };
    Expr {
        e: Box::new(new_e),
        typ: expr.typ,
        ctx: expr.ctx,
        pos: expr.pos,
    }
}

fn substitute_stmt(stmt: Stmt, name: &str, replacement: &Expr) -> Stmt {
    let new_s = match *stmt.s {
        SNode::Decl(e1, t, e2) => SNode::Decl(
            Box::new(substitute_variable(*e1, name, replacement)),
            t,
            Box::new(substitute_variable(*e2, name, replacement)),
        ),
        SNode::Expr(e1) => SNode::Expr(Box::new(substitute_variable(*e1, name, replacement))),
        SNode::Print(e1) => SNode::Print(Box::new(substitute_variable(*e1, name, replacement))),
        SNode::TypeDecl(h, d) => SNode::TypeDecl(h, d),
    };
    Stmt {
        s: Box::new(new_s),
        ctx: stmt.ctx,
        pos: stmt.pos,
    }
}

/// Lower a bare abstraction `\x : T => e` to a closure.
///
/// The abstraction compiles to `func.func @closure_N(x, env) -> ret` where
/// `env` holds the free variables of the body that are in scope here (the
/// captures); the closure value allocated in the current block stores the
/// function address plus those captures.
pub(crate) fn lower_abstraction<'c, 'a>(
    expr: &Expr,
    binding: &Binding,
    body: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let Binding(name, param_type) = binding;
    let param_mono = match &param_type.t {
        Monotype::TypeFuncApplication(f, _) if matches!(**f, TypeFunc::Infer) => {
            concrete_parts(&expr.typ)
                .map(|(param, _)| param)
                .ok_or_else(|| {
                    format!(
                        "codegen: abstraction parameter type not resolved for `{}`",
                        name
                    )
                })?
        }
        _ => param_type.t.clone(),
    };
    let param_mlir = lower_type(&param_mono, module)?;
    let env_i64 = IntegerType::new(module.context, 64).into();

    // Captures: free variables of the body that are bound in the enclosing
    // environment. Their values are available here (at closure creation) and
    // are loaded from the `env` pointer inside the compiled function.
    let free = free_variables(body);
    let mut captures: Vec<(String, Value<'c, 'a>, Type<'c>)> = Vec::new();
    for (name, entry) in env.iter() {
        if free.contains(name) {
            match entry {
                EnvEntry::Value(value) => captures.push((name.clone(), *value, value.r#type())),
                EnvEntry::Abstraction(sym) => {
                    if let Some(info) = module.abstractions.get(sym) {
                        let concrete = default_free_vars(&info.abs_type);
                        let mlir_type = lower_type(&concrete, module)?;
                        let ref_val = reference_specialization(sym, name, &concrete, block, module)?;
                        captures.push((name.clone(), ref_val, mlir_type));
                    } else if let Some(info) = module.abstractions.get(name) {
                        let concrete = default_free_vars(&info.abs_type);
                        let mlir_type = lower_type(&concrete, module)?;
                        let ref_val = reference_specialization(name, name, &concrete, block, module)?;
                        captures.push((name.clone(), ref_val, mlir_type));
                    } else {
                        return Err(format!(
                            "codegen: cannot capture lambda binding `{name}` in a closure yet"
                        ));
                    }
                }
            }
        }
    }

    let symbol = format!("closure_{}", module.closures);
    module.closures += 1;
    let location = Location::unknown(module.context);

    if captures.is_empty() {
        let closure_block = Block::new(&[(param_mlir, location)]);
        let arg: Value<'c, 'a> = closure_block.argument(0).map_err(|e| e.to_string())?.into();
        let mut closure_env = HashMap::new();
        closure_env.insert(name.clone(), EnvEntry::Value(arg));

        let body_value = lower_expr(body, &closure_block, module, &mut closure_env)?;
        closure_block.append_operation(func::r#return(&[body_value], location));

        let function_type =
            FunctionType::new(module.context, &[param_mlir], &[body_value.r#type()]);
        let region = Region::new();
        region.append_block(closure_block);

        let function = func::func(
            module.context,
            StringAttribute::new(module.context, &symbol),
            TypeAttribute::new(function_type.into()),
            region,
            &[],
            location,
        );
        module.module.body().append_operation(function);
        module.functions += 1;

        block
            .append_operation(func::constant(
                module.context,
                FlatSymbolRefAttribute::new(module.context, &symbol),
                function_type,
                location,
            ))
            .result(0)
            .map_err(|e| e.to_string())
            .map(Into::into)
    } else {
        let closure_block = Block::new(&[(param_mlir, location), (env_i64, location)]);
        let arg = closure_block.argument(0).map_err(|e| e.to_string())?.into();
        let env_arg_i64: Value<'c, 'a> = closure_block
            .argument(1)
            .map_err(|e| e.to_string())?
            .into();
        let mut closure_env = HashMap::new();
        closure_env.insert(name.clone(), EnvEntry::Value(arg));

        let env_ptr = Type::parse(module.context, "!llvm.ptr")
            .ok_or_else(|| "codegen: failed to create `!llvm.ptr`".to_string())?;
        let inttoptr = OperationBuilder::new("llvm.inttoptr", location)
            .add_operands(&[env_arg_i64])
            .add_results(&[env_ptr])
            .build()
            .map_err(|e| e.to_string())?;
        let env_arg: Value<'c, 'a> = closure_block
            .append_operation(inttoptr)
            .result(0)
            .map_err(|e| e.to_string())?
            .into();
        let env_struct = env_struct_type(module, &captures)?;
        for (i, (capture, _, typ)) in captures.iter().enumerate() {
            let value = load_field(
                module,
                &closure_block,
                env_arg,
                env_struct,
                i as i32,
                *typ,
                location,
            )?;
            closure_env.insert(capture.clone(), EnvEntry::Value(value));
        }

        let body_value = lower_expr(body, &closure_block, module, &mut closure_env)?;
        closure_block.append_operation(func::r#return(&[body_value], location));

        let function_type =
            FunctionType::new(module.context, &[param_mlir, env_i64], &[body_value.r#type()]);
        let region = Region::new();
        region.append_block(closure_block);

        let function = func::func(
            module.context,
            StringAttribute::new(module.context, &symbol),
            TypeAttribute::new(function_type.into()),
            region,
            &[(
                Identifier::new(module.context, "llvm.emit_c_interface"),
                Attribute::unit(module.context),
            )],
            location,
        );
        module.module.body().append_operation(function);
        module.functions += 1;

        build_closure(module, block, &symbol, &captures, location)
    }
}

/// Lower a literal to an `arith.constant`, returning its SSA value.
pub(crate) fn lower_literal<'c, 'a>(
    lit: &Lit,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
) -> Result<Value<'c, 'a>, String> {
    match lit {
        // Strings live in a module-level global and need several ops.
        Lit::Str(value) => lower_string(value, block, module),
        _ => {
            let location = Location::unknown(module.context);
            let operation = match lit {
                Lit::Int(value) => arith::constant(
                    module.context,
                    IntegerAttribute::new(
                        IntegerType::new(module.context, 32).into(),
                        *value as i64,
                    )
                    .into(),
                    location,
                ),
                Lit::Float(value) => arith::constant(
                    module.context,
                    FloatAttribute::new(module.context, Type::float32(module.context), *value as f64)
                        .into(),
                    location,
                ),
                Lit::Bool(value) => arith::constant(
                    module.context,
                    BoolAttribute::new(module.context, *value).into(),
                    location,
                ),
                Lit::Unit => arith::constant(
                    module.context,
                    IntegerAttribute::new(IntegerType::new(module.context, 32).into(), 0).into(),
                    location,
                ),
                Lit::Str(_) => unreachable!(),
            };
            // The op must be appended to the block before its results are used,
            // otherwise it is destroyed when `operation` drops and `value` dangles.
            block
                .append_operation(operation)
                .result(0)
                .map_err(|e| e.to_string())
                .map(Into::into)
        }
    }
}

/// Lower a string literal to a module-level `llvm.mlir.global` plus
/// `llvm.mlir.addressof` and `llvm.getelementptr`, returning `!llvm.ptr`.
fn lower_string<'c, 'a>(
    value: &str,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
) -> Result<Value<'c, 'a>, String> {
    let context = module.context;
    let location = Location::unknown(context);

    let symbol = format!("str_{}", module.strings);
    module.strings += 1;

    let bytes = value.len() + 1; // trailing NUL
    let array_type = Type::parse(context, &format!("!llvm.array<{bytes} x i8>"))
        .ok_or_else(|| format!("codegen: failed to create `!llvm.array<{bytes} x i8>`"))?;
    let ptr_type = Type::parse(context, "!llvm.ptr")
        .ok_or_else(|| "codegen: failed to create `!llvm.ptr`".to_string())?;

    // `llvm.mlir.global private @str_N = "value\0" : !llvm.array<N x i8>`
    let global = OperationBuilder::new("llvm.mlir.global", location)
        .add_attributes(&[
            (
                Identifier::new(context, "sym_name"),
                StringAttribute::new(context, &symbol).into(),
            ),
            (
                Identifier::new(context, "value"),
                StringAttribute::new(context, &format!("{value}\0")).into(),
            ),
            (
                Identifier::new(context, "global_type"),
                TypeAttribute::new(array_type).into(),
            ),
        ])
        .add_regions([Region::new()])
        .build()
        .map_err(|e| e.to_string())?;
    module.module.body().append_operation(global);

    // `llvm.mlir.addressof @str_N : !llvm.ptr`
    let addressof = OperationBuilder::new("llvm.mlir.addressof", location)
        .add_attributes(&[(
            Identifier::new(context, "global_name"),
            FlatSymbolRefAttribute::new(context, &symbol).into(),
        )])
        .add_results(&[ptr_type])
        .build()
        .map_err(|e| e.to_string())?;
    let array_ptr = block.append_operation(addressof).result(0).map_err(|e| e.to_string())?;

    // `llvm.getelementptr %0[0, 0] : (!llvm.ptr) -> !llvm.ptr`
    let gep = llvm::get_element_ptr(
        context,
        array_ptr.into(),
        DenseI32ArrayAttribute::new(context, &[0, 0]),
        array_type,
        ptr_type,
        location,
    );
    block
        .append_operation(gep)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}
