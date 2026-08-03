//! Top-level statements and declarations.

use crate::ast::*;
use crate::types::{Monotype, TypeFunc};
use melior::dialect::{func, llvm};
use melior::ir::{
    attribute::{FlatSymbolRefAttribute, StringAttribute, TypeAttribute},
    operation::OperationBuilder,
    r#type::{FunctionType, IntegerType},
    Block, BlockLike, Identifier, Location, Region, RegionLike, Type, Value, ValueLike,
};
use std::collections::HashMap;

use super::{AbstractionInfo, EnumLayout, Env, Module};
use super::expr::lower_expr;
use super::types::lower_type;

/// Lower a type-checked program to an MLIR module.
///
/// `context` is borrowed and must outlive the returned module; the REPL owns
/// it so bindings can be appended across input lines.
///
/// Returns an error string if any statement cannot be lowered (e.g. an AST
/// node with no dialect mapping yet).
pub fn lower<'a>(prog: &Program, context: &'a melior::Context) -> Result<Module<'a>, String> {
    let mut module = Module::new(context);

    // The entry function `@__main` is built statement by statement; the value
    // of the last expression statement becomes its `func.return`.
    let entry_block = Block::new(&[]);
    let mut last_value: Option<Value<'a, '_>> = None;
    for stmt in &prog.stmts {
        if let Some(value) = lower_stmt(stmt, &mut module, &entry_block)? {
            last_value = Some(value);
        }
    }

    // Finish the entry body before moving `entry_block` into the module.
    let location = Location::unknown(context);
    let outputs: Vec<Type<'a>> = match last_value {
        Some(value) => {
            let typ = value.r#type();
            entry_block.append_operation(func::r#return(&[value], location));
            vec![typ]
        }
        None => {
            entry_block.append_operation(func::r#return(&[], location));
            vec![]
        }
    };

    emit_entry_function(&mut module, entry_block, &outputs)?;
    Ok(module)
}

// ----------------------------------------------------------------------------
// Statements
// ----------------------------------------------------------------------------

fn lower_stmt<'a, 'b>(
    stmt: &Stmt,
    module: &mut Module<'a>,
    entry: &'b Block<'a>,
) -> Result<Option<Value<'a, 'b>>, String> {
    match &*stmt.s {
        SNode::TypeDecl(h, t) => {
            lower_type_decl(h, t, module)?;
            Ok(None)
        }
        SNode::Decl(e1, t, e2) => {
            lower_decl(e1, t, e2, module)?;
            Ok(None)
        }
        SNode::Expr(e1) => lower_expr_stmt(e1, module, entry).map(Some),
        SNode::Print(e1) => {
            let mut env = HashMap::new();
            lower_print_stmt(e1, module, entry, &mut env)?;
            Ok(None)
        }
    }
}

/// Lower a top-level expression statement `e;` into the entry function body.
///
/// The produced value is tracked by [`lower`] and becomes the `func.return`
/// of `@__main` if this is the last statement.
fn lower_expr_stmt<'a, 'b>(
    expr: &Expr,
    module: &mut Module<'a>,
    entry: &'b Block<'a>,
) -> Result<Value<'a, 'b>, String> {
    let mut env = HashMap::new();
    lower_expr(expr, entry, module, &mut env)
}

/// Lower a `print e;` statement to an `llvm.call @printf` on `e`.
///
/// The type checker guarantees `e : str`, so the lowered value is a
/// `!llvm.ptr`, which is exactly what `printf` expects.
pub(crate) fn lower_print_stmt<'a, 'b>(
    expr: &Expr,
    module: &mut Module<'a>,
    entry: &'b Block<'a>,
    env: &mut Env<'a, 'b>,
) -> Result<(), String> {
    let value = lower_expr(expr, entry, module, env)?;
    ensure_printf(module)?;

    let location = Location::unknown(module.context);
    let call = OperationBuilder::new("llvm.call", location)
        .add_attributes(&[(
            Identifier::new(module.context, "callee"),
            FlatSymbolRefAttribute::new(module.context, "printf").into(),
        )])
        .add_operands(&[value])
        .add_results(&[IntegerType::new(module.context, 32).into()])
        .build()
        .map_err(|e| e.to_string())?;
    entry.append_operation(call);
    Ok(())
}

/// Emit the external declaration `llvm.func @printf(!llvm.ptr) -> i32`
/// exactly once.
fn ensure_printf<'a>(module: &mut Module<'a>) -> Result<(), String> {
    if module.printf_declared {
        return Ok(());
    }
    let location = Location::unknown(module.context);
    let ptr = Type::parse(module.context, "!llvm.ptr")
        .ok_or_else(|| "codegen: failed to create `!llvm.ptr`".to_string())?;
    let function_type = FunctionType::new(
        module.context,
        &[ptr],
        &[IntegerType::new(module.context, 32).into()],
    );
    let function = llvm::func(
        module.context,
        StringAttribute::new(module.context, "printf"),
        TypeAttribute::new(function_type.into()),
        Region::new(),
        &[],
        location,
    );
    module.module.body().append_operation(function);
    module.printf_declared = true;
    Ok(())
}

/// Materialize the entry function `@__main` with the given result types.
///
/// Its body is the accumulated top-level statements; an empty result list
/// means the function returns unit.
fn emit_entry_function<'a>(
    module: &mut Module<'a>,
    entry: Block<'a>,
    outputs: &[Type<'a>],
) -> Result<(), String> {
    let location = Location::unknown(module.context);
    let function_type = FunctionType::new(module.context, &[], outputs);
    let region = Region::new();
    region.append_block(entry);

    let function = func::func(
        module.context,
        StringAttribute::new(module.context, "__main"),
        TypeAttribute::new(function_type.into()),
        region,
        &[],
        location,
    );
    module.module.body().append_operation(function);
    module.functions += 1;
    Ok(())
}

// ----------------------------------------------------------------------------
// Declarations
// ----------------------------------------------------------------------------

/// Lower a top-level `let x : T = e;` binding to a `func.func`.
///
/// A binding becomes a nullary symbol `@x` whose result type is `T` (or, for
/// an unannotated binding, the type of the lowered initializer) and whose
/// body lowers `e` and `func.return`s it.
///
/// When the initializer is a lambda, no symbol is emitted: the abstraction is
/// registered in [`Module::abstractions`] and specialized on demand for every
/// concrete type it is used at, so a polymorphic function like `let id =
/// \x => x;` can be applied at `int` and `bool` independently.
pub fn lower_decl<'a>(
    e1: &Expr,
    typ: &crate::ast::Type,
    e2: &Expr,
    module: &mut Module<'a>,
) -> Result<(), String> {
    let name = match &*e1.e {
        ENode::Variable(n) => n.clone(),
        _ => {
            return Err(format!(
                "codegen: expected a variable name in declaration, got {:?}",
                *e1.e
            ))
        }
    };

    if let ENode::Abstraction(binding, body) = &*e2.e {
        module.abstractions.insert(
            name,
            AbstractionInfo {
                param: binding.0.clone(),
                param_type: binding.1.t.clone(),
                body: (**body).clone(),
                abs_type: e2.typ.clone(),
            },
        );
        return Ok(());
    }

    let location = Location::unknown(module.context);

    // An unannotated binding carries `infer`; its result type is taken from
    // the initializer's lowered value instead.
    let declared_type = match &typ.t {
        Monotype::TypeFuncApplication(f, _) if matches!(**f, TypeFunc::Infer) => None,
        _ => Some(lower_type(&typ.t, module)?),
    };

    // Build the body first: `func.func` is constructed with the final return
    // type, which for unannotated bindings only exists after lowering `e2`.
    let block = Block::new(&[]);
    let mut env = HashMap::new();
    let value = lower_expr(e2, &block, module, &mut env)?;
    block.append_operation(func::r#return(&[value], location));

    let result_type = match declared_type {
        Some(t) => t,
        None => value.r#type(),
    };
    let function_type = FunctionType::new(module.context, &[], &[result_type]);

    let region = Region::new();
    region.append_block(block);

    let function = func::func(
        module.context,
        StringAttribute::new(module.context, &name),
        TypeAttribute::new(function_type.into()),
        region,
        &[],
        location,
    );
    module.module.body().append_operation(function);
    module.symbols.insert(name.clone(), function_type);
    module.functions += 1;
    Ok(())
}

// ----------------------------------------------------------------------------
// Type declarations
// ----------------------------------------------------------------------------

/// Lower a type declaration by registering it in `module`.
///
/// A `TypeDecl` emits no MLIR operations; it only records the type so that
/// later uses of it in `lower_type` can be resolved:
///   - `enum E <tvars> = ...`  registers [`EnumLayout`] under the enum name.
///   - `type E <tvars> = T`    registers the alias' expanded right-hand side
///                             under the alias name.
///
/// The type checker has already rejected duplicate/conflicting declarations,
/// so the name collisions checked here are defensive only.
pub fn lower_type_decl<'a>(
    header: &TypeHeader,
    dec: &TypeDec,
    module: &mut Module<'a>,
) -> Result<(), String> {
    match dec {
        TypeDec::Enum(variants) => {
            if module.enums.contains_key(&header.n) || module.aliases.contains_key(&header.n) {
                return Err(format!("codegen: type `{}` is already declared", header.n));
            }
            let layout = EnumLayout {
                params: header.tvars.clone(),
                variants: variants
                    .iter()
                    .map(|v| {
                        (
                            v.n.clone(),
                            v.tparams.iter().map(|t| t.t.clone()).collect(),
                        )
                    })
                    .collect(),
            };
            for (index, variant) in variants.iter().enumerate() {
                module.constructors.insert(
                    variant.n.clone(),
                    (header.n.clone(), index, variant.tparams.len()),
                );
            }
            module.enums.insert(header.n.clone(), layout);
        }
        TypeDec::Alias(rhs) => {
            if module.aliases.contains_key(&header.n) || module.enums.contains_key(&header.n) {
                return Err(format!("codegen: type `{}` is already declared", header.n));
            }
            module.aliases.insert(header.n.clone(), rhs.t.clone());
        }
    }
    Ok(())
}
