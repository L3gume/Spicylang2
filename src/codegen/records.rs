//! Record layout: canonical field order and struct construction/extraction.

use crate::types::{Monotype, TypeFunc};
use melior::dialect::llvm;
use melior::ir::attribute::DenseI64ArrayAttribute;
use melior::ir::{Block, BlockLike, Location, Type, Value};

use super::Module;

/// Walk a closed record type `Rec(RowExt(..))` into its `(label, field type)`
/// list in row order. Errors on anything but a closed row (an open row
/// variable tail means the record was not fully resolved before codegen).
pub(crate) fn record_fields(typ: &Monotype) -> Result<Vec<(String, Monotype)>, String> {
    let row = match typ {
        Monotype::TypeFuncApplication(f, args) if matches!(**f, TypeFunc::Rec) && args.len() == 1 => {
            &args[0]
        }
        _ => return Err(format!("codegen: expected a record type, got {typ:?}")),
    };
    let mut fields = Vec::new();
    let mut cur = row;
    loop {
        match cur {
            Monotype::TypeFuncApplication(f, args) if matches!(**f, TypeFunc::EmptyRow) => break,
            Monotype::TypeFuncApplication(f, args)
                if matches!(**f, TypeFunc::RowExt(_)) && args.len() == 2 =>
            {
                let label = match &**f {
                    TypeFunc::RowExt(l) => l.clone(),
                    _ => unreachable!(),
                };
                fields.push((label, args[0].clone()));
                cur = &args[1];
            }
            _ => return Err(format!("codegen: record row is not closed: {row:?}")),
        }
    }
    Ok(fields)
}

/// Index of `label` in `fields`, or an error if absent.
pub(crate) fn field_index(fields: &[(String, Monotype)], label: &str) -> Result<usize, String> {
    fields
        .iter()
        .position(|(name, _)| name == label)
        .ok_or_else(|| format!("codegen: record has no field `{label}`"))
}

/// An undefined value of `struct_type` (`llvm.mlir.undef`), the starting point
/// for building a record field-by-field.
pub(crate) fn record_undef<'c, 'a>(
    block: &'a Block<'c>,
    struct_type: Type<'c>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    block
        .append_operation(llvm::undef(struct_type, location))
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Insert `value` at field `index` of the record `container`, returning the new
/// struct value (`llvm.insertvalue`).
pub(crate) fn insert_field<'c, 'a>(
    module: &Module<'c>,
    block: &'a Block<'c>,
    container: Value<'c, 'a>,
    index: i32,
    value: Value<'c, 'a>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let position = DenseI64ArrayAttribute::new(module.context, &[index as i64]);
    block
        .append_operation(llvm::insert_value(
            module.context,
            container,
            position,
            value,
            location,
        ))
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}

/// Extract field `index` of `container` as `result_type` (`llvm.extractvalue`).
pub(crate) fn extract_field<'c, 'a>(
    module: &Module<'c>,
    block: &'a Block<'c>,
    container: Value<'c, 'a>,
    index: i32,
    result_type: Type<'c>,
    location: Location<'c>,
) -> Result<Value<'c, 'a>, String> {
    let position = DenseI64ArrayAttribute::new(module.context, &[index as i64]);
    block
        .append_operation(llvm::extract_value(
            module.context,
            container,
            position,
            result_type,
            location,
        ))
        .result(0)
        .map_err(|e| e.to_string())
        .map(Into::into)
}
