# Row Types for SpicyLang Records

This document describes how to replace SpicyLang's *nominal* record types with
*structural* record types based on **row polymorphism**, and the steps required
to implement it. It assumes the current state of `src/types.rs` (Hindley–Milner
inference via Algorithm-W with a `Monotype`/`TypeFunc` representation, nominal
`TypeFunc::Record(String)` records, and `record_signatures` in `TypeContext`).

---

## Motivation

The current records are nominal: a record value's type is `Record(name)[args]`,
and the field layout lives in `record_signatures`, not in the type itself. Field
access can only be resolved when the scrutinee's type is already a concrete
`Record(name)` — a value whose type is still a type variable (e.g. `\x => x.name`)
cannot be resolved, because a bare type variable carries no information about
which record/field it refers to.

Row types make records *structural*: the type itself lists its fields, plus a
**row variable** standing for "the rest of the fields". Field access then just
unifies the scrutinee's type with `{ name: α | ρ }`, which constrains *any* type
— including a type variable — without needing to know which record it is.

This restores full HM compatibility: `\x => x.name` becomes typable as
`∀ρ α. { name: α | ρ } → α`.

---

## The model

A **row** is either:

* a row variable `ρ`,
* the empty row `∅`, or
* an extension `(l : τ; ρ)` — field `l` of type `τ`, followed by the rest `ρ`.

A **record type** is a row wrapped by a record constructor: `{ ρ }`.

```
record type   { x: Int, y: Bool }        (closed; ρ = ∅)
open record   { x: Int | ρ }             (ρ is a row variable)
field access  e.l : τ      where e : { (l : τ; ρ) }
```

Because label ordering is irrelevant, rows unify up to **commutation**:

```
unify((l₁ : τ₁; ρ₁), (l₂ : τ₂; ρ₂)) =
    l₁ == l₂  ⇒  unify(τ₁, τ₂) ∪ unify(ρ₁, ρ₂)
    l₁ != l₂  ⇒  ρ₃ fresh;
                 unify(ρ₁, (l₂ : τ₂; ρ₃)) ∪ unify(ρ₂, (l₁ : τ₁; ρ₃))
```

This commutation rule is what makes records unordered and is the main new
complexity in `unify` (see Phase 1).

---

## Representation in the existing type system

The `Monotype = TypeVariable(String) | TypeFuncApplication(Box<TypeFunc>, Vec<Monotype>)`
shape is retained; row types are encoded as new `TypeFunc` constructors:

| Constructor | Arity | Meaning |
|-------------|-------|---------|
| `TypeFunc::Rec` | 1 | `{ ρ }` — a record type wrapping one row |
| `TypeFunc::RowExt(String)` | 2 | `(l : τ; ρ)` — field `l`, args `[τ, ρ]` |
| `TypeFunc::EmptyRow` | 0 | `∅` — the empty row |

Row variables are ordinary `TypeVariable`s (a fresh type variable stands for an
unknown row). A closed record `{ x: Int, y: Bool }` becomes:

```
Rec( RowExt("x")[ Int, RowExt("y")[ Bool, EmptyRow ] ] )
```

`TypeFunc::Record(String)`, `RecordSignature`, `record_names`, and
`record_signatures` are removed (see Phase 3). The existing generic helpers
(`apply`, `instantiate`, `free_variables`, `contains`) already recurse over
`TypeFuncApplication` uniformly, so `Rec`/`RowExt`/`EmptyRow` are handled by
them with no change.

### Typing rules

```
Field access (α, ρ fresh):
    Γ ⊢ e : σ     unify(σ, Rec(RowExt(l)[α, ρ]))
    -------------------------------------------
              Γ ⊢ e.l : α

Construction (closed record):
    Γ ⊢ vᵢ : τᵢ   for each field lᵢ = vᵢ
    --------------------------------------------------
    Γ ⊢ { lᵢ = vᵢ } : Rec(RowExt(l₁)[τ₁, …, ∅ …])

Record pattern (αᵢ, ρ fresh):
    unify(scrutinee, Rec(RowExt(l₁)[α₁, … RowExt(lₙ)[αₙ, ρ] …]))
    each pattern variable xᵢ gets αᵢ
```

---

## Design decisions

These are the open choices to settle before/while implementing; recommendations
are given.

1. **Keep `record` declarations?** *(Recommended: keep them as aliases.)*
   The syntax `record Person = { name: str, age: int }` can stay, but it should
   desugar to a *type alias* `Person = { name: Str, age: Int | ∅ }` rather than
   a nominal constructor. Construction `Person { … }`, patterns `Person { … }`,
   and field access then all work structurally via the row type. This reuses the
   existing `type_aliases`/`expand` machinery and lets `TypeFunc::Record`,
   `record_signatures`, etc. be deleted.

2. **`with` semantics.** *(Recommended: update-only, Phase 1.)*
   The current `with` only *changes* existing fields. Update-only needs no
   "lacks" machinery: for each `(l = v)`, unify the scrutinee with
   `Rec(RowExt(l)[τ_l, ρ])`, check `v : τ_l`, and the result is the scrutinee's
   type. *Extending* a record with a new field (width change) additionally
   requires a **lacks** constraint (`ρ` must not already contain `l`), which is
   significantly harder (negative constraints). Defer extension to Phase 2.

3. **Record patterns: open or closed?** *(Recommended: open.)*
   With structural records, `Person { bar: n, … }` should match any record that
   *has* `bar`, binding `n`; the row variable `ρ` captures the fields not named.
   This is idiomatic for row types and matches the existing
   `Foo { bar: n, baz: opt }` pattern in `programs/record.spcy` (which lists two
   of the record's fields).

4. **Field ordering in codegen.** Rows are unordered, but memory layout is not;
   codegen must fix a canonical layout — sort fields by label name at
   record-construction time so the LLVM struct layout is deterministic.

---

## Implementation steps

### Phase 0 — Representation (`src/types.rs`)

1. Add `TypeFunc::Rec`, `TypeFunc::RowExt(String)`, `TypeFunc::EmptyRow` to the
   `TypeFunc` enum (line 11).
2. Add convenience constructors on `Monotype` (one per `TypeFunc` variant's
   arity) and remove `Monotype::record` / `TypeFunc::Record`:

   * `empty_row() -> Monotype` — no args; the `∅` tail that ends a row.
   * `row_ext(label: String, field: Monotype, rest: Monotype) -> Monotype` —
     `label` is the field name, `field` is the field's type, and `rest` is the
     rest of the row (a further `row_ext`, a row variable, or `empty_row`).
     Produces `(label : field; rest)`.
   * `rec(row: Monotype) -> Monotype` — wraps a `row` to form a record type
     `{ row }`.

   `rest` and `rec`'s argument must be *rows* (never field types or record
   types); this is enforced by construction and by the Phase 1 unification
   rules, not by the Rust types. Composition:

       { x: Int, y: Bool }  =  rec(row_ext("x", int(), row_ext("y", bool(), empty_row())))
       { x: Int | ρ }       =  rec(row_ext("x", int(), var("ρ")))
       {}                   =  rec(empty_row())
3. Update `Display for Monotype` (line 31) to print `{ l: τ, … }` (and
   `(l : τ; ρ)` for a bare row, if ever shown).
4. This immediately breaks the non-exhaustive `match **f` sites in
   `src/display.rs:27` and `src/codegen/types.rs:17` — add arms for the three
   new constructors (display trivially; codegen in Phase 4).

### Phase 1 — Row unification (`src/types.rs`, `unify`, line 394)

The current `unify(typ1, typ2)` is structural and, crucially, has **no source of
fresh type variables** — but the commutation rule must allocate a fresh row
variable. So the first change is mechanical: give `unify` access to the type-var
counter. Recommended: change the signature to

    unify(context: &mut TypeContext, typ1: &Monotype, typ2: &Monotype) -> Result<Substitution, UnificationError>

and update every call site (there are ~15 in `types.rs`) to pass `context`. The
alternative is a dedicated `unify_row(context, ρ₁, ρ₂)` helper plus a `&mut u32`
counter; changing `unify`'s signature is simpler and keeps all unification in
one place.

Second, insert a **dedicated row branch before the generic
`TypeFuncApplication` pointwise case**. The generic case compares `f1 != f2` and
unifies arguments pointwise, which is wrong for rows: `RowExt("x")` and
`RowExt("y")` are *different* constructors, so the generic case would reject
them instead of commuting. The row constructors must therefore never reach the
generic case. Put the row logic in a helper:

```
unify_row(context, ρ₁, ρ₂):
    match (ρ₁, ρ₂):
        (TypeVariable v, _)    => bind v ↦ ρ₂            (occurs-check)
        (_, TypeVariable v)    => bind v ↦ ρ₁            (occurs-check)
        (EmptyRow, EmptyRow)   => Ok(empty)
        (EmptyRow, RowExt _)   => Err("row width mismatch")
        (RowExt _, EmptyRow)   => Err("row width mismatch")
        (RowExt(l₁)[τ₁, ρ₁'], RowExt(l₂)[τ₂, ρ₂']):
            l₁ == l₂  =>  s = unify(τ₁, τ₂)
                          combine(s, unify_row(ρ₁'.apply(s), ρ₂'.apply(s)))
            l₁ != l₂  =>  ρ₃ = context.new_typevar()
                          s₁ = unify(ρ₁', RowExt(l₂)[τ₂, ρ₃])
                          s₂ = unify(ρ₂'.apply(s₁), RowExt(l₁)[τ₁.apply(s₁), ρ₃.apply(s₁)])
                          combine(s₁, s₂)
```

And in `unify`, add cases that route through `unify_row`:

```
Rec ρ₁  ~  Rec ρ₂        => unify_row(ρ₁, ρ₂)
Rec ρ   ~  TypeVariable v => bind v ↦ Rec ρ      (already handled by the generic var case)
```

(`Rec` vs a bare row does not arise in normal inference; the `Rec ~ Rec` and the
type-variable cases are the ones that matter.)

Notes:

* The **commutation case** is the crux: two different labels share a fresh tail
  `ρ₃`, and each "missing" field is folded into the other row's tail. The exact
  `apply`/`combine` ordering above must be preserved — applying `s₁` before
  building the second equation keeps the fresh `ρ₃` and already-resolved vars
  consistent.
* The **occurs-check already works for rows as-is**: `Monotype::contains` (line
  93) recurses through `TypeFuncApplication` arguments, so
  `unify(ρ, RowExt(l)[τ, ρ])` is rejected as "Infinite recursive type" because
  `ρ` occurs in its own tail.
* The generic pointwise case (the `f1 != f2` / zip-over-args case) stays
  unchanged for `Fn`/`List`/`Enum`/etc., but must be guaranteed never to see
  `Rec`/`RowExt`/`EmptyRow` — those are consumed by the row branch first.
* Because `RowExt` carries its label, `f1 != f2` would already distinguish
  `RowExt("x")` from `RowExt("y")`; the dedicated branch turns that difference
  into commutation rather than an error.

This is the hardest part of the feature. Write unit tests for `unify_row` in
isolation (same-label, different-label, width mismatch, infinite row) before
wiring up the inference rules.

### Phase 2 — Inference rules (`src/types.rs`)

1. **`infer_field_access` (line 920).** Infer the scrutinee, create fresh `α`
   and `ρ`, unify the scrutinee's type with `Rec(RowExt(f)[α, ρ])`, and return
   `α`. Delete the `TypeVariable` `todo!()` — this is now the *normal* path that
   makes `\x => x.name` typable. Return `s1.combine(s_unify)` and `α` (applied).
2. **`infer_record` (line 952).** Infer each field value; build the closed row
   from all fields and return `Rec(...)` as the type. No signature lookup.
3. **`infer_with` (line 956).** Infer the scrutinee; for each `(l = v)` unify
   the scrutinee with `Rec(RowExt(l)[τ_l, ρ])` and `v` with `τ_l`. Result is the
   scrutinee's type (update-only).
4. **`type_pattern` — `ENode::Record` (line 1029).** Unify the match type with a
   `Rec` row built from the pattern's field names, binding each sub-pattern to
   the corresponding field type; `ρ` fresh for the remaining fields.

### Phase 3 — `record` declarations as aliases (`src/types.rs`)

1. In `handle_type_decl`'s `TypeDec::Record` arm (line 555), build the closed
   row from the declared `Binding`s and register it as a `TypeAlias` via
   `add_alias` (reuse `type_to_typefn`/`expand` to elaborate the field types,
   instantiating the record's type parameters).
2. Remove `TypeFunc::Record`, `RecordSignature`, `record_names`,
   `record_signatures`, `add_record_signature`, `get_record_signature`, and
   `has_record_name`.
3. Simplify `expand` (line 471): the `Enum(name)` branch's record-resolution
   case (added earlier to bridge the nominal gap) becomes unnecessary — record
   names are now plain aliases, already handled by the existing `Some(alias)`
   branch.

### Phase 4 — Display, codegen, and type resolution

1. `src/display.rs:27` — render row/record types.
2. `src/codegen/types.rs:17` — map a closed `Rec` row to an LLVM struct; sort
   fields by label for a stable layout; reuse/extend the existing record codegen
   stubs.
3. `resolve_expr_types` (line 1123) — implement the `FieldAccess`/`Record`/`With`
   arms (currently `todo!()`, line 1176) to recurse into their children so the
   final substitution reaches scrutinee/field/pattern types.
4. `ENode::Record`/`FieldAccess`/`With` `Display`/`PartialEq` in `ast.rs` (the
   `todo!()` at line 334 and the `resolve`/`typecheck` call sites).

### Phase 5 — Tests

* `tests/types.rs`: field access on a type variable (`\x => x.name`), `with`
  update, record construction, record patterns.
* `programs/record.spcy`: already exercises construction, field access, `with`,
  and a record pattern — use it as the end-to-end target once codegen lands.
* Exhaustiveness and error cases: accessing a missing field, `with` on a
  non-record, infinite-row occurs-check.

---

## Hardest parts / risks

1. **Row unification with commutation.** The label-reordering rule interacts
   subtly with the occurs-check and with `Substitution::combine`; get this right
   and write dedicated unit tests before touching the inference rules.
2. **`with` extension (lacks).** If width-changing `with` is ever wanted, it
   needs negative constraints on row variables, which Algorithm-W does not
   express naturally — likely a real constraint-solver extension.
3. **Codegen layout.** Rows are unordered but memory layout is not; the
   canonical (label-sorted) layout must be consistent between construction,
   field access, and `with`, or runtime values will be misaligned.
4. **Error messages.** Nominal records give clean "no field `x` on `Person`"
   errors; structural records give "cannot unify `{ x: α | ρ }` with `Int`",
   which is noisier. Plan to special-case `Rec`/`RowExt` in error reporting.

---

## References

* Wand, "Complete type inference for simple objects" (1987) — row unification.
* Rémy, "Type inference for records in a natural extension of ML" (1989).
* Gaster & Jones, "A polymorphic type system for extensible records and
  variants" — the commutation formulation used above.
