//! List representation: cons cells on the heap.

use crate::ast::*;
use crate::types::{Monotype, TypeFunc};
use melior::dialect::{arith, func, llvm};
use melior::dialect::llvm::LoadStoreOptions;
use melior::ir::{
    attribute::{DenseI32ArrayAttribute, FlatSymbolRefAttribute, IntegerAttribute, StringAttribute, TypeAttribute},
    operation::OperationBuilder,
    r#type::{FunctionType, IntegerType},
    Block, BlockLike, Identifier, Location, Region, Type, Value,
};

use super::{Env, Module};
use super::apply::default_free_vars;
use super::expr::lower_expr;
use super::types::lower_type;

// ----------------------------------------------------------------------------
// Lists
// ----------------------------------------------------------------------------

/// Extract the element type of `list T`.
pub(crate) fn list_elem(typ: &Monotype) -> Option<Monotype> {
    match typ {
        Monotype::TypeFuncApplication(f, args)
            if matches!(**f, TypeFunc::List) && args.len() == 1 =>
        {
            Some(args[0].clone())
        }
        _ => None,
    }
}

/// The type of a cons cell `{ head: T, tail: !llvm.ptr }` for element `elem`.
pub(crate) fn cell_struct_type<'c>(module: &Module<'c>, elem: Type<'c>) -> Result<Type<'c>, String> {
    let elem_str = elem.to_string();
    Type::parse(module.context, &format!("!llvm.struct<({elem_str}, !llvm.ptr)>")).ok_or_else(
        || {
            format!(
                "codegen: failed to create cons cell type `!llvm.struct<({elem_str}, !llvm.ptr)>`"
            )
        },
    )
}

/// Emit the external declaration `func.func @malloc(i64) -> i64` once.
/// Uses `func.func` with only built-in types so the `func_to_llvm` pass
/// can convert it cleanly.
pub(crate) fn ensure_malloc<'a>(module: &mut Module<'a>) -> Result<(), String> {
    if module.malloc_declared {
        return Ok(());
    }
    let location = Location::unknown(module.context);
    let function_type = FunctionType::new(
        module.context,
        &[IntegerType::new(module.context, 64).into()],
        &[IntegerType::new(module.context, 64).into()],
    );
    let function = func::func(
        module.context,
        StringAttribute::new(module.context, "malloc"),
        TypeAttribute::new(function_type.into()),
        Region::new(),
        &[(
            Identifier::new(module.context, "sym_visibility"),
            StringAttribute::new(module.context, "private").into(),
        )],
        location,
    );
    module.module.body().append_operation(function);
    module.malloc_declared = true;
    Ok(())
}

/// Append an `llvm.call @malloc(bytes)` to `block`, returning the pointer.
pub(crate) fn malloc_call<'c, 'a>(
    module: &mut Module<'c>,
    block: &'a Block<'c>,
    bytes: i64,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    ensure_malloc(module)?;
    let ptr = Type::parse(module.context, "!llvm.ptr")
        .ok_or_else(|| "codegen: failed to create `!llvm.ptr`".to_string())?;
    let size = integer_constant(module, block, 64, bytes, location)?;

    let call = func::call(
        module.context,
        FlatSymbolRefAttribute::new(module.context, "malloc"),
        &[size],
        &[IntegerType::new(module.context, 64).into()],
        location,
    );
    let raw_i64: Value<'c, 'a> = block
        .append_operation(call)
        .result(0)
        .map_err(|e| e.to_string())?
        .into();

    let inttoptr = OperationBuilder::new("llvm.inttoptr", location)
        .add_operands(&[raw_i64])
        .add_results(&[ptr])
        .build()
        .map_err(|e| e.to_string())?;
    block
        .append_operation(inttoptr)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Append a constant of value `n` with the given bit width to `block`.
pub(crate) fn integer_constant<'c, 'a>(
    module: &Module<'c>,
    block: &'a Block<'c>,
    bits: u32,
    value: i64,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let op = arith::constant(
        module.context,
        IntegerAttribute::new(IntegerType::new(module.context, bits).into(), value).into(),
        location,
    );
    block
        .append_operation(op)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// The empty list: a null pointer.
pub(crate) fn empty_list<'c, 'a>(
    block: &'a Block<'c>,
    module: &Module<'c>,
) -> Result<Value<'c, 'a>, String> {
    let ptr = Type::parse(module.context, "!llvm.ptr")
        .ok_or_else(|| "codegen: failed to create `!llvm.ptr`".to_string())?;
    let op = llvm::zero(ptr, Location::unknown(module.context));
    block
        .append_operation(op)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Whether a list pointer is the empty list (`null`).
pub(crate) fn list_is_null<'c, 'a>(
    ptr: Value<'c, 'a>,
    block: &'a Block<'c>,
    module: &Module<'c>,
) -> Result<Value<'c, 'a>, String> {
    let location = Location::unknown(module.context);
    let int_op = OperationBuilder::new("llvm.ptrtoint", location)
        .add_operands(&[ptr])
        .add_results(&[IntegerType::new(module.context, 64).into()])
        .build()
        .map_err(|e| e.to_string())?;
    let intv: Value<'c, 'a> = block
        .append_operation(int_op)
        .result(0)
        .map_err(|e| e.to_string())?
        .into();
    let zero = integer_constant(module, block, 64, 0, location)?;
    let cmp = arith::cmpi(module.context, arith::CmpiPredicate::Eq, intv, zero, location);
    block
        .append_operation(cmp)
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Build a cons cell `{ head, tail }` on the heap and return its pointer.
pub(crate) fn build_cons<'c, 'a>(
    head: Value<'c, 'a>,
    tail: Value<'c, 'a>,
    head_mono: &Monotype,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
) -> Result<Value<'c, 'a>, String> {
    let location = Location::unknown(module.context);
    let elem = lower_type(&default_free_vars(head_mono), module)?;
    let ptr = Type::parse(module.context, "!llvm.ptr")
        .ok_or_else(|| "codegen: failed to create `!llvm.ptr`".to_string())?;
    let struct_type = cell_struct_type(module, elem)?;

    let cell = malloc_call(module, block, 16, location)?;

    let head_op = llvm::get_element_ptr(
        module.context,
        cell,
        DenseI32ArrayAttribute::new(module.context, &[0, 0]),
        struct_type,
        ptr,
        location,
    );
    let head_addr: Value<'c, 'a> = block
        .append_operation(head_op)
        .result(0)
        .map_err(|e| e.to_string())?
        .into();
    block.append_operation(llvm::store(
        module.context,
        head,
        head_addr,
        location,
        LoadStoreOptions::new(),
    ));

    let tail_op = llvm::get_element_ptr(
        module.context,
        cell,
        DenseI32ArrayAttribute::new(module.context, &[0, 1]),
        struct_type,
        ptr,
        location,
    );
    let tail_addr: Value<'c, 'a> = block
        .append_operation(tail_op)
        .result(0)
        .map_err(|e| e.to_string())?
        .into();
    block.append_operation(llvm::store(
        module.context,
        tail,
        tail_addr,
        location,
        LoadStoreOptions::new(),
    ));

    Ok(cell)
}

/// Lower `[e1, ..., en]` by folding `::` from the end onto the empty list.
pub(crate) fn lower_list<'c, 'a>(
    exps: &[Expr],
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let mut result = empty_list(block, module)?;
    for e in exps.iter().rev() {
        let head = lower_expr(e, block, module, env)?;
        result = build_cons(head, result, &e.typ, block, module)?;
    }
    Ok(result)
}

/// Lower `x::xs` to a fresh cons cell with head `x` and tail `xs`.
pub(crate) fn lower_cons<'c, 'a>(
    head: &Expr,
    tail: &Expr,
    block: &'a Block<'c>,
    module: &mut Module<'c>,
    env: &mut Env<'c, 'a>,
) -> Result<Value<'c, 'a>, String> {
    let head_value = lower_expr(head, block, module, env)?;
    let tail_value = lower_expr(tail, block, module, env)?;
    build_cons(head_value, tail_value, &head.typ, block, module)
}