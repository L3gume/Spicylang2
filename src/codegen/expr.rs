//! Expression lowering.

use crate::ast::*;
use crate::types::{Monotype, TypeFunc};
use melior::dialect::{arith, scf};
use melior::ir::{
    attribute::{BoolAttribute, IntegerAttribute},
    operation::OperationBuilder,
    r#type::IntegerType,
    Block, BlockLike, Location, Operation, Region, RegionLike, Type, Value,
};

use super::{Env, EnvEntry, Module};
use super::closures::pattern_bound_vars;
use super::apply::{
    bind_in_env, default_free_vars, lower_abstraction, lower_application, lower_let, lower_literal,
    lower_variable,
};
use super::enums::{
    PatternBind, destructure_pattern, enum_disc_eq, enum_variant_fields,
};
use super::lists::{list_elem, list_is_null, lower_cons, lower_list};
use super::types::lower_type;

// ----------------------------------------------------------------------------
// Expressions
// ----------------------------------------------------------------------------

/// Lower `expr` to MLIR ops inside the current function body, returning the
/// SSA value it produces.
///
/// Pointer map (ENode variant -> dialect ops):
///   Block(stmts, e)         -> emit statements into a nested region, return `e`
///   Match(scrut, cases)     -> `scf.if` chain on the discriminant
///   List(es)                -> heap-allocate via `llvm` malloc, or a struct
///                              header + element buffer
///   Cons(h, t)              -> prepend to a list header struct
pub(crate) fn lower_expr<'c, 'a>(
    expr: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let location = module.location(&expr.pos);
    match &*expr.e {
        ENode::Literal(lit) => lower_literal(lit, block, module, location),
        ENode::Variable(_) => lower_variable(expr, block, module, env, location),
        ENode::Abstraction(binding, body) => {
            lower_abstraction(expr, binding, body, block, module, env, location)
        }
        ENode::Application(f, x) => lower_application(f, x, block, module, env, location),
        ENode::Let(name, e1, e2) => lower_let(name, e1, e2, block, module, env, location),
        ENode::IfElse(c, t, e) => lower_ifelse(c, t, e, &expr.typ, block, module, env, location),
        ENode::Block(stmts, e) => lower_block(stmts, e, block, module, env),
        ENode::Match(scrut, cases) => lower_match(scrut, cases, &expr.typ, block, module, env),
        ENode::Comparison(op, a, b) => lower_comparison(op, a, b, block, module, env, location),
        ENode::Arithmetic(op, a, b) => lower_arith(op, a, b, block, module, env, location),
        ENode::Logical(op, a, b) => lower_logical(op, a, b, block, module, env, location),
        ENode::Unary(op, e) => lower_unary(op, e, block, module, env, location),
        ENode::List(es) => lower_list(es, block, module, env, location),
        ENode::Cons(h, t) => lower_cons(h, t, block, module, env, location),
    }
}

/// Primitive kinds that binary/unary operators dispatch on.
enum Prim {
    Int,
    Float,
    Bool,
    Str,
}

/// Classify a (defaulted) primitive type; anything else is not a scalar
/// operand for these operators.
fn primitive_kind(typ: &Monotype) -> Result<Prim, String> {
    match default_free_vars(typ) {
        Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::Int => Ok(Prim::Int),
        Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::Float => Ok(Prim::Float),
        Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::Bool => Ok(Prim::Bool),
        Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::Str => Ok(Prim::Str),
        other => Err(format!(
            "codegen: unsupported operand type for binary/unary operation: {other:?}"
        )),
    }
}

/// Build a generic two-operand `arith` op with result type inference.
fn arith_binop<'c>(
    name: &str,
    lhs: Value<'c, '_>,
    rhs: Value<'c, '_>,
    location: Location<'c>,
) -> Result<Operation<'c>, String> {
    OperationBuilder::new(name, location)
        .add_operands(&[lhs, rhs])
        .enable_result_type_inference()
        .build()
        .map_err(|e| e.to_string())
}

/// Append a constant of value `n` of type `i32` to `block`.
fn i32_constant<'c, 'a>(
    module: &Module<'c>,
    block: &'a Block<'c>,
    n: i64,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let op = arith::constant(
        module.context,
        IntegerAttribute::new(IntegerType::new(module.context, 32).into(), n).into(),
        location,
    );
    block
        .append_operation(op)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Append a `true`/`false` `i1` constant to `block`.
fn bool_constant<'c, 'a>(
    module: &Module<'c>,
    block: &'a Block<'c>,
    b: bool,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let op = arith::constant(
        module.context,
        BoolAttribute::new(module.context, b).into(),
        location,
    );
    block
        .append_operation(op)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Lower `a OP b` to the integer or float `arith` op selected by the operand
/// type.
fn lower_arith<'c, 'a>(
    op: &ArithOp,
    e1: &Expr,
    e2: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let lhs = lower_expr(e1, block, module, env)?;
    let rhs = lower_expr(e2, block, module, env)?;

    let op_name = match (op, primitive_kind(&e1.typ)?) {
        (ArithOp::Plus, Prim::Int) => "arith.addi",
        (ArithOp::Plus, Prim::Float) => "arith.addf",
        (ArithOp::Plus, Prim::Str) => {
            return Err("codegen: string concatenation not implemented".to_string())
        }
        (ArithOp::Minus, Prim::Int) => "arith.subi",
        (ArithOp::Minus, Prim::Float) => "arith.subf",
        (ArithOp::Times, Prim::Int) => "arith.muli",
        (ArithOp::Times, Prim::Float) => "arith.mulf",
        (ArithOp::Div, Prim::Int) => "arith.divsi",
        (ArithOp::Div, Prim::Float) => "arith.divf",
        (ArithOp::Mod, Prim::Int) => "arith.remsi",
        (ArithOp::Mod, Prim::Float) => {
            return Err("codegen: float modulo not implemented".to_string())
        }
        (_, Prim::Bool) => {
            return Err("codegen: arithmetic on booleans is not supported".to_string())
        }
        (_, Prim::Str) => {
            return Err("codegen: arithmetic on strings is not supported".to_string())
        }
    };

    block
        .append_operation(arith_binop(op_name, lhs, rhs, location)?)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Lower `a OP b` to `arith.cmpi` (int/bool) or `arith.cmpf` (float).
fn lower_comparison<'c, 'a>(
    op: &CompOp,
    e1: &Expr,
    e2: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let lhs = lower_expr(e1, block, module, env)?;
    let rhs = lower_expr(e2, block, module, env)?;

    let operation = match primitive_kind(&e1.typ)? {
        Prim::Int | Prim::Bool => {
            let predicate = match op {
                CompOp::Eq => arith::CmpiPredicate::Eq,
                CompOp::NotEq => arith::CmpiPredicate::Ne,
                CompOp::Less => arith::CmpiPredicate::Slt,
                CompOp::Greater => arith::CmpiPredicate::Sgt,
                CompOp::LessEq => arith::CmpiPredicate::Sle,
                CompOp::GreatEq => arith::CmpiPredicate::Sge,
            };
            arith::cmpi(module.context, predicate, lhs, rhs, location)
        }
        Prim::Float => {
            let predicate = match op {
                CompOp::Eq => arith::CmpfPredicate::Oeq,
                CompOp::NotEq => arith::CmpfPredicate::One,
                CompOp::Less => arith::CmpfPredicate::Olt,
                CompOp::Greater => arith::CmpfPredicate::Ogt,
                CompOp::LessEq => arith::CmpfPredicate::Ole,
                CompOp::GreatEq => arith::CmpfPredicate::Oge,
            };
            arith::cmpf(module.context, predicate, lhs, rhs, location)
        }
        Prim::Str => {
            return Err("codegen: string comparison not implemented".to_string())
        }
    };

    block
        .append_operation(operation)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Lower `a OP b` to `arith.andi` / `arith.ori` / `arith.xori` (i1).
fn lower_logical<'c, 'a>(
    op: &LogicalOp,
    e1: &Expr,
    e2: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let lhs = lower_expr(e1, block, module, env)?;
    let rhs = lower_expr(e2, block, module, env)?;
    let op_name = match op {
        LogicalOp::And => "arith.andi",
        LogicalOp::Or => "arith.ori",
        LogicalOp::Xor => "arith.xori",
    };
    block
        .append_operation(arith_binop(op_name, lhs, rhs, location)?)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Lower `-e` (int: `subi 0, e`; float: `arith.negf`) and `!e` (`xori e, true`).
fn lower_unary<'c, 'a>(
    op: &UnaryOp,
    e: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let value = lower_expr(e, block, module, env)?;

    match op {
        UnaryOp::Negate => match primitive_kind(&e.typ)? {
            Prim::Int => {
                let zero = i32_constant(module, block, 0, location)?;
                block
                    .append_operation(arith_binop("arith.subi", zero, value, location)?)
                    .result(0)
                    .map_err(|e| e.to_string())
                    .map(Into::into)
            }
            Prim::Float => {
                let op = OperationBuilder::new("arith.negf", location)
                    .add_operands(&[value])
                    .enable_result_type_inference()
                    .build()
                    .map_err(|e| e.to_string())?;
                block
                    .append_operation(op)
                    .result(0)
                    .map_err(|e| e.to_string())
                    .map(Into::into)
            }
            _ => Err("codegen: unary negation requires an int or float operand".to_string()),
        },
        UnaryOp::Not => {
            let one = bool_constant(module, block, true, location)?;
            block
                .append_operation(arith_binop("arith.xori", value, one, location)?)
                .result(0)
                .map_err(|e| e.to_string())
                .map(Into::into)
        }
    }
}

/// Lower `if c then t else e` to `scf.if`, returning its result value.
///
/// Each branch gets its own copy of the environment (so branch-local bindings
/// do not leak out) and yields its lowered value; the result type is the
/// `if` expression's resolved type, with free type variables defaulted.
fn lower_ifelse<'c, 'a>(
    cond: &Expr,
    then_branch: &Expr,
    else_branch: &Expr,
    result_mono: &Monotype,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let condition = lower_expr(cond, block, module, env)?;
    let result_type = lower_type(&default_free_vars(result_mono), module)?;

    let mut then_env = env.clone();
    let then_block = Block::new(&[]);
    let then_value = lower_expr(then_branch, &then_block, module, &mut then_env)?;
    then_block.append_operation(scf::r#yield(&[then_value], location));
    let then_region = Region::new();
    then_region.append_block(then_block);

    let mut else_env = env.clone();
    let else_block = Block::new(&[]);
    let else_value = lower_expr(else_branch, &else_block, module, &mut else_env)?;
    else_block.append_operation(scf::r#yield(&[else_value], location));
    let else_region = Region::new();
    else_region.append_block(else_block);

    let if_op = scf::r#if(condition, &[result_type], then_region, else_region, location);
    block
        .append_operation(if_op)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Lower a block expression `{ stmt; ...; e }`: run its statements in a
/// cloned environment (block-local bindings do not leak out) and return the
/// final expression's value.
fn lower_block<'c, 'a>(
    stmts: &[Stmt],
    final_expr: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let mut block_env = env.clone();
    for stmt in stmts {
        lower_block_stmt(stmt, block, module, &mut block_env)?;
    }
    lower_expr(final_expr, block, module, &mut block_env)
}

/// Lower a statement that appears inside a block expression: declarations
/// become local SSA bindings (unlike top-level declarations, which become
/// symbols).
fn lower_block_stmt<'c, 'a>(
    stmt: &Stmt,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<(), String> {
    match &*stmt.s {
        SNode::Decl(e1, _, e2) => {
            let name = match &*e1.e {
                ENode::Variable(n) => n.clone(),
                _ => {
                    return Err(format!(
                        "codegen: expected a variable name in declaration, got {:?}",
                        *e1.e
                    ))
                }
            };
            bind_in_env(&name, e2, block, module, env)
        }
        SNode::Expr(e1) => {
            lower_expr(e1, block, module, env)?;
            Ok(())
        }
        SNode::TypeDecl(_, _) => Err(
            "codegen: type declarations are not allowed inside block expressions".to_string(),
        ),
    }
}

/// Lower `match scrut | pat => e | ...` to an `scf.if` chain. Patterns: a
/// literal compares for equality, `[]` tests for an empty list, `x::xs`
/// destructures a cons cell, and a final variable pattern is the catch-all
/// else branch.
fn lower_match<'c, 'a>(
    scrutinee: &Expr,
    cases: &[MatchCase],
    result_mono: &Monotype,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let location = module.location(&scrutinee.pos);
    let scrut = lower_expr(scrutinee, block, module, env)?;
    let result_type = lower_type(&default_free_vars(result_mono), module)?;
    let scrut_typ = default_free_vars(&scrutinee.typ);
    // The cons-cell element type, for `x::xs` patterns on a list scrutinee.
    let elem_mlir = match list_elem(&scrut_typ) {
        Some(e) => Some(lower_type(&e, module)?),
        None => None,
    };
    lower_match_cases(
        scrut,
        &scrut_typ,
        cases,
        0,
        result_type,
        elem_mlir,
        location,
        block,
        module,
        env,
    )
}

fn lower_match_cases<'c, 'a: 'b, 'b>(
    scrut: Value<'c, 'a>,
    scrut_typ: &Monotype,
    cases: &[MatchCase],
    index: usize,
    result_type: Type<'c>,
    elem_mlir: Option<Type<'c>>,
    location: Location<'c>,
    block: &'b Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'b>, String> {
    if index == cases.len() {
        // Defensive: the type checker rejects non-exhaustive matches.
        return Err("codegen: non-exhaustive match".to_string());
    }
    let case = &cases[index];
    let last = index + 1 == cases.len();

    // A catch-all variable pattern matches anything and must be last. Enum
    // constructor names (e.g. `None`) are not catch-alls.
    if let ENode::Variable(name) = &*case.val.e {
        if !module.constructors.contains_key(name) {
            if !last {
                return Err(format!(
                    "codegen: catch-all pattern `{name}` must be the last case"
                ));
            }
            let mut case_env = env.clone();
            case_env.insert(name.clone(), EnvEntry::Value(scrut));
            return lower_expr(&case.exp, block, module, &mut case_env);
        }
    }

    // The bindings this pattern produces (loaded in the branch body) and, for
    // constructor patterns, the discriminant it must equal.
    let (binding, ctor_index) = match &*case.val.e {
        ENode::Literal(_) => (None, None),
        ENode::List(es) if es.is_empty() => (None, None),
        ENode::Cons(hd, tl) => {
            let (hd_name, tl_name) = match (&*hd.e, &*tl.e) {
                (ENode::Variable(h), ENode::Variable(t)) => (h.clone(), t.clone()),
                _ => {
                    return Err(
                        "codegen: only `x::xs` cons patterns are supported".to_string()
                    )
                }
            };
            let elem = elem_mlir
                .ok_or_else(|| "codegen: cons pattern requires a list scrutinee".to_string())?;
            (
                Some(PatternBind::Cons {
                    head_name: hd_name,
                    head_type: elem,
                    tail_name: tl_name,
                }),
                None,
            )
        }
        // `Some x` binds the constructor's payload field.
        ENode::Application(ctor, arg) => {
            let ctor_name = match &*ctor.e {
                ENode::Variable(n) => n.clone(),
                _ => {
                    return Err(format!(
                        "codegen: unsupported match pattern {:?}",
                        *case.val.e
                    ))
                }
            };
            let &(ref enum_name, variant_index, arity) = module
                .constructors
                .get(&ctor_name)
                .ok_or_else(|| {
                    format!("codegen: unsupported match pattern {:?}", *case.val.e)
                })?;
            if arity != 1 {
                return Err(format!(
                    "codegen: constructor pattern `{ctor_name}` with arity {arity} is not supported"
                ));
            }
            let bound = pattern_bound_vars(arg);
            if bound.len() != 1 {
                return Err(
                    "codegen: only single-variable constructor patterns are supported"
                        .to_string(),
                );
            }
            let fields = enum_variant_fields(module, scrut_typ, enum_name, variant_index)?;
            let field_type = lower_type(&default_free_vars(&fields[0]), module)?;
            (
                Some(PatternBind::Enum(vec![(bound[0].clone(), field_type)])),
                Some(variant_index),
            )
        }
        // A nullary constructor pattern `None`.
        ENode::Variable(name) => {
            let &(_, variant_index, arity) = module.constructors.get(name).ok_or_else(|| {
                format!("codegen: unsupported match pattern {:?}", *case.val.e)
            })?;
            if arity != 0 {
                return Err(format!(
                    "codegen: constructor pattern `{name}` with arity {arity} is not supported"
                ));
            }
            (None, Some(variant_index))
        }
        other => {
            return Err(format!(
                "codegen: unsupported match pattern {:?}",
                *other
            ))
        }
    };

    // The last case is guaranteed to match (exhaustiveness), so lower it
    // directly instead of wrapping it in one more `scf.if`.
    if last {
        let mut case_env = env.clone();
        for (name, value) in destructure_pattern(binding, scrut, block, module, location)? {
            case_env.insert(name, EnvEntry::Value(value));
        }
        return lower_expr(&case.exp, block, module, &mut case_env);
    }

    // The condition for this case.
    let cond: Value<'c, 'b> = match &*case.val.e {
        // `lit => e` matches when `scrut == lit`.
        ENode::Literal(lit) => {
            let pattern = lower_literal(lit, block, module, location)?;
            let cmp = arith::cmpi(
                module.context,
                arith::CmpiPredicate::Eq,
                scrut,
                pattern,
                location,
            );
            block
                .append_operation(cmp)
                .result(0)
                .map_err(|e| e.to_string())?
                .into()
        }
        // `[] => e` matches when the list is empty (null).
        ENode::List(_) => list_is_null(scrut, block, module, location)?,
        // `x::xs => e` matches when the list is non-empty.
        ENode::Cons(..) => {
            let is_null = list_is_null(scrut, block, module, location)?;
            let one = bool_constant(module, block, true, location)?;
            let not_null_op = arith_binop("arith.xori", is_null, one, location)?;
            block
                .append_operation(not_null_op)
                .result(0)
                .map_err(|e| e.to_string())?
                .into()
        }
        // `Some x` / `None` match on the discriminant.
        _ => {
            let index = ctor_index.ok_or_else(|| {
                "codegen: internal error: missing constructor index".to_string()
            })?;
            enum_disc_eq(module, block, scrut, index, location)?
        }
    };

    let mut then_env = env.clone();
    let then_block = Block::new(&[]);
    for (name, value) in destructure_pattern(binding, scrut, &then_block, module, location)? {
        then_env.insert(name, EnvEntry::Value(value));
    }
    let then_value = lower_expr(&case.exp, &then_block, module, &mut then_env)?;
    then_block.append_operation(scf::r#yield(&[then_value], location));
    let then_region = Region::new();
    then_region.append_block(then_block);

    let else_block = Block::new(&[]);
    let else_value = lower_match_cases(
        scrut,
        scrut_typ,
        cases,
        index + 1,
        result_type,
        elem_mlir,
        location,
        &else_block,
        module,
        env,
    )?;
    else_block.append_operation(scf::r#yield(&[else_value], location));
    let else_region = Region::new();
    else_region.append_block(else_block);

    let if_op = scf::r#if(cond, &[result_type], then_region, else_region, location);
    block
        .append_operation(if_op)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}
