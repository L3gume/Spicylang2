# Record Codegen: Layouts and MLIR

This document describes how Merlin's *structural* record types (see
`docs/rowtypes.md`) are lowered to MLIR. It covers two things:

1. how the canonical field **layout** is enforced (declaration order), and
2. how the MLIR for record construction / field access / `with` is emitted.

Records are **stack-allocated** in the sense of *value semantics*: a record is
an immutable `!llvm.struct<(T1, T2, ...)>` SSA value, never heap-allocated. A
`with` expression copies the struct (updating one or more fields), leaving the
original untouched.

---

## 0. Representation: SSA struct values

A record value is an immutable `!llvm.struct<(T1, T2, ...)>` built with
`llvm.mlir.undef` + `llvm.insertvalue`, read with `llvm.extractvalue`. LLVM
keeps the value in registers or spills to the stack as needed — no `malloc` or
`alloca`.

```text
{ name = "x", age = 3 }   =>  %r = llvm.mlir.undef : !llvm.struct<(!llvm.ptr, i32)>
                              %0 = llvm.insertvalue "x", %r[0]
                              %1 = llvm.insertvalue 3, %0[1]
r.age                      =>  %v = llvm.extractvalue %r[1]
r with { age = 4 }         =>  %u = llvm.insertvalue 4, %r[1]
```

Because struct SSA values are copied on update, `with` producing a new record
(while leaving the scrutinee unchanged) is automatic.

---

## 1. Enforcing layouts

Field order must follow the **declaration**, but the current code loses that
information in three places:

- The record **name is thrown away** at parse time: `grammar.lalrpop` parses
  `<n:Name>` for `Foo { .. }` but drops `n` into `ENode::Record(fs)`. Record
  patterns have the same problem.
- `infer_record` builds the row in **use-site order**, so
  `Foo { age = 3, name = "x" }` and `Foo { name = "x", age = 3 }` resolve to
  structurally-equal but differently-ordered rows.
- `lower_type_decl`'s `TypeDec::Record` arm is a `"Not Implemented yet"` stub,
  so codegen has no declaration to consult.

### Approach

1. **Retain the name** — `ENode::Record` becomes `Record(Option<String>,
   Vec<FieldAssn>)`, threaded through the parser (and record patterns).
2. **Canonicalize at the type checker** — `infer_record`, given a name, looks
   up the record's `TypeAlias` (registered in declaration order by
   `handle_type_decl`), instantiates it to the canonical closed row, and
   unifies each `field = value` against the corresponding declared field type.
   Every record value then has a declaration-ordered `.typ`, and missing /
   unknown fields become clean type errors.
3. **Register a `RecordLayout` in codegen** — `Module` gains
   `records: HashMap<String, RecordLayout>` (mirroring `EnumLayout`), populated
   in `lower_type_decl`'s `TypeDec::Record` arm. `RecordLayout` carries the
   field list in declaration order plus the header's type parameters.

Once construction is canonical, `with` (which preserves the scrutinee's row)
and field access (which reads it) inherit the order automatically.

---

## 2. Generating MLIR

- **`lower_type` (`Rec` arm)** — walk the resolved closed row, lower each field
  type, and emit `!llvm.struct<(T1, T2, ...)>`. Error on a tail that is not
  `EmptyRow`/`RowExt`.
- **`lower_expr` `Record`** — resolve the canonical field list (name →
  `RecordLayout`, reordering `field_assns` into declaration order); lower each
  field value; `undef` + `insertvalue` per field.
- **`lower_expr` `FieldAccess`** — lower the scrutinee; find the field's index
  in the scrutinee's row; `extractvalue`. Result type is the field's lowered
  type.
- **`lower_expr` `With`** — lower the scrutinee (an SSA struct value); for each
  `(l = v)`, lower `v`, find `l`'s index in the scrutinee's row, `insertvalue`.
  Returns the new struct value.
- **Record patterns** — extend `case_pattern`/`destructure_pattern` with a
  `PatternBind::Record` that `extractvalue`s each bound variable at its index in
  the *scrutinee's* canonical row (the pattern may list fields out of order;
  binding order ≠ layout order).
- **`free_variables`** — `FieldAccess(e, _) => fv(e)`,
  `Record(_, fs) => union over exp`, `With(e, fs) => fv(e) ∪ union over exp`.
- **`resolve_expr_types`** already recurses correctly — no change.

### Helpers

```rust
fn record_fields(m: &Monotype) -> Result<Vec<(String, Monotype)>, String>  // walk Rec(RowExt..) -> [(label, ty)]
fn field_index(fields: &[(String, Monotype)], label: &str) -> usize
```

---

## Gotchas

- **`default_free_vars` corrupts open rows.** It maps any `TypeVariable` to
  `int`, so an open-row tail `ρ` becomes `int` inside the record type. This is
  safe only because records reach codegen *closed* (construction canonicalizes
  and substitution resolves `ρ`); the `Rec` arm of `lower_type` should still
  reject a non-`EmptyRow`/`RowExt` tail rather than emit garbage.
- **Field access has no name**, so it relies on the scrutinee being canonical —
  which holds iff construction is name-canonicalized. Decide whether anonymous
  `{ ... }` construction is legal at all (the grammar already requires
  `Name { ... }`).
- **Parametric records** (`Poly 'a = { bar: 'a }`): `RecordLayout` carries
  `params`; substitute them when instantiating, like `enum_variant_fields`.

---

## Implementation order

1. AST + parser: retain the record name (`ENode::Record(Option<String>, ..)` +
   patterns).
2. `RecordLayout` registry + `lower_type_decl` `Record` arm + `record_fields` /
   `field_index` helpers.
3. `infer_record` name-canonicalization (make every record type
   declaration-ordered).
4. `lower_type` `Rec` arm, then `Record`/`FieldAccess`/`With` lowering, then
   patterns.
5. `free_variables` arms; end-to-end with `programs/record.mln`.
