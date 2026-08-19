# Builtin Functions and Standard Library

Plan for adding unlowerable builtin functions (string conversions, `print`/`println`)
to the typing context and a prelude/standard library to the language.

## Overview

Two layers, because they need different treatment:

1. **Unlowerable builtins** — `print`, `println`, `int_to_str`, `float_to_str`,
   `bool_to_str`. Seeded as polytypes in the context (so inference is free), then
   lowered as *real first-class MLIR functions* (so no special dispatch anywhere).
2. **Prelude** — `map`, `filter`, `length`, `append`, `reverse`, `foldl/r`, etc.
   Written in Merlin itself, injected into every program, and run through the
   *existing* lambda-specialization machinery. Zero new compiler code for these.

Design rationale (vs. the alternatives):

- **Reserved keyword list + special inference rules**: rejected. The type system is
  full HM (`TypeContext` maps `String -> Polytype`, types.rs:302; `algo_w`
  instantiates/generalises; `Application` unifies via fresh type vars,
  types.rs:597-605). Hand-writing inference rules for builtins would duplicate
  that logic and break interaction with the substitution machinery, polymorphism,
  and user-defined higher-order uses. A keyword list also bakes a fixed set into
  the lexer and prevents builtins from being first-class values (e.g. `map print`).
- **AST nodes (the current `print` pattern)**: rejected. `print` costs a grammar
  production (grammar.lalrpop:96), an `SNode::Print` variant, a typecheck case
  (types.rs:668), free-variable handling (closures.rs:63), and a codegen case
  (stmt.rs:89) — and still only works as a statement taking an `Atom`. Scaling
  that to ~10 builtins multiplies the bloat.

---

## Phase 1 — Seed builtins into the typing context

**1a. Builtin polytypes** (`src/types.rs`)

- Add a const list + helper in `types.rs`, and seed `TypeContext::new()`
  (types.rs:308) right after initialization:
  - `print : str -> unit`, `println : str -> unit`
  - `int_to_str : int -> str`, `float_to_str : float -> str`, `bool_to_str : bool -> str`
  - (optional, cheap) `int_to_float : int -> float`
- Build these with the existing `Monotype::func` / `int()` / `string()` helpers
  (types.rs:205, 189, 197) wrapped in `Polytype::Mono`.
- **Seeding in `new()` is deliberate**: the grammar's `Prog` action
  (grammar.lalrpop:14), `Stmt::from` (ast.rs:71), and the REPL (main.rs:169) all
  call it, so builtins are uniformly present everywhere with no other wiring. The
  test suite has been checked — nothing asserts `TypeContext::new()` has an empty
  `variables` map.

**1b. Redefinition guard** (`src/types.rs`)

- Add `TypeContext::is_builtin(&str)` backed by the const list (no new field
  needed; mirrors how `enum_names` is handled, types.rs:336).
- Error on redefinition in the three binding sites: `Stmt::typecheck` Decl
  (ast.rs:79-100), `Let` (types.rs:606-623), and Block `Decl` (types.rs:641-662).
  Codegen dispatches builtins by name, so shadowing would silently miscompile.

**1c. No inference changes.** The existing `Application` case (types.rs:597)
already unifies `int_to_str 42` against `int -> str`. `int_to_str 3.14` fails
with a type error for free. That is the whole payoff of seeding over "special
inference rules".

---

## Phase 2 — Lower builtins as first-class functions (`src/codegen/`)

**2a. `print`/`println` become named `func.func`s** — emitted once per module from
a new `register_runtime_builtins(module)` (called from `lower`, stmt.rs:27):

- `@print(!llvm.ptr)` with the body of the existing `lower_print_stmt`
  (stmt.rs:114-144), i.e. ptrtoint + `printf`.
- `@println(!llvm.ptr)` = printf on the arg + printf on a `"\n"` string global
  (reuse the `strings` counter, mod.rs:115).
- Insert both into `module.symbols` (mod.rs:122). Then `print "hi"` — and even
  `map print xs` — lowers through the *ordinary* application path
  (`lower_variable` at apply.rs:354 → `call_indirect` at apply.rs:550). **No new
  dispatch in `lower_application`.**

**2b. Conversions as libc-backed functions:**

- Emit `@int_to_str(i32) -> !llvm.ptr` etc. calling `snprintf` into a `malloc`'d
  buffer (`malloc_declared` flag already exists, mod.rs:119; printf already
  resolves in the JIT, so snprintf will too).
- Bool → `"true"`/`"false"`; float via `%g` (decide precision explicitly).
- Register in `module.symbols`; same ordinary call path as print.

**2c. Delete the `print` AST node** (this *shrinks* the codebase):

- grammar.lalrpop:96 — drop `"print" <e:Atom>` from `BlockStmt`
- ast.rs — `SNode::Print` variant, typecheck case (106-113), `resolve_stmt_types`
  case (156)
- types.rs — Block case (668-675)
- codegen/closures.rs:63, codegen/stmt.rs:89, codegen/expr.rs:385

After this, `print x` is just `Application(Variable("print"), x)` via `Name`.

---

## Phase 3 — Prelude

**3a. Location.** New `src/prelude.rs` with `include_str!("prelude.mln")` and a
`OnceLock<Vec<Stmt>>` that parses it once. Written in the language: lambdas,
`match`, cons, recursion, arithmetic — all of which exist.

**3b. Injection points** — the tricky part. It cannot live inside `Program::parse`,
because the REPL calls `parse` per line (main.rs:161) and would re-append the
prelude every line. Instead:

- Keep `Program::parse` (ast.rs:293) **pure** (no prelude) — this also keeps the
  7 stmt-count assertions in the ast.rs tests (e.g. ast.rs:327) green.
- Add `Program::parse_with_prelude(buf)`: parse, then prepend a clone of the
  cached prelude stmts.
- File mode: use it at main.rs:49.
- REPL: seed `accumulated_stmts` (main.rs:136) with prelude stmts **once** at
  session start. Each subsequent line re-typechecks/re-lowers the whole
  accumulated list, which already happens, so prelude fns are just re-registered
  (idempotent).

**3c. Contents (first cut):** `map`, `filter`, `length`, `append`, `reverse`,
`foldl`, `foldr`, `take`, `drop`, `sum`/`product` (monomorphic int versions — HM
can't overload, same reason as `int_to_str`). Everything is a polymorphic
`let <name> = \... => ...;`.

**3d. Why this composes with existing machinery (the key insight):** a prelude
`let map = \f => \xs => match xs | [] => [] | (h :: t) => f h :: map f t;` is
just a polymorphic lambda binding. `lower_decl` registers it in
`module.abstractions` (stmt.rs:235), and every use site specializes it at its
concrete type via `specialize_binding` (apply.rs:386) — the exact path user
`let id = \x => x` already takes. Cross-references between prelude fns work
because they're all registered before user code lowers (`lower_variable` falls
through to `module.abstractions`, apply.rs:338); recursion works via `self_name`
(apply.rs:446). **So prelude = pure reuse, no new codegen or inference.**

---

## Phase 4 — Ripple effects to handle

- **REPL classification** (main.rs:182-205): `print "hi"` has type `str -> unit`,
  an `Fn`, so the `is_fn` check at main.rs:186 routes it to the DeclFn branch and
  it never executes. Need: if the last statement is an application of a
  unit-returning builtin, execute and print nothing.
- **`%` in printed strings**: the existing printf-ptr-to-i64 hack (stmt.rs:124)
  only prints strings without format specifiers. Keep the limitation or fix when
  wrapping `@print`; flag it, don't scope-creep.
- **Shadowing policy**: builtins reserved (Phase 1b), prelude names *shadowable*
  (they're ordinary context entries — a user `let map` overwrites, matching the
  "prelude is just source" philosophy).
- **Float formatting**: pick and document `%g` precision so `float_to_str` is
  deterministic.

---

## Phase 5 — Tests and verification

- **Typecheck unit tests** (`ast.rs`/`types.rs`): `int_to_str 42 : str`;
  wrong-arg-type error; `map print`; redefinition of a builtin errors; shadowing
  a prelude name is allowed.
- **Integration**: a `programs/prelude.mln` exercising conversions +
  `map`/`filter`/`length` end-to-end, plus `map print` to prove print is
  first-class.
- **Regression**: run the existing suite — the only expected churn is the deleted
  `SNode::Print` tests.

---

## Estimated footprint

~2-3 new functions in codegen, one const list + guard in types.rs, a prelude
source file, and one new parse entry point.
