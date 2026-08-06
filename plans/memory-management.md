# Memory Management: Arena, Refcounting, and a Rust-style Lifetime System

Plan for giving SpicyLang sound memory management. The goal is to end the current
state where `itostr` buffers and list cons cells are `malloc`'d and never freed,
so a long-lived REPL session (or a tight loop inside one program) leaks
unbounded memory.

The document surveys four strategies, recommends a phased path, and spends the
most detail on the ambitious one the project wants to try: a compile-time
**ownership + lifetime analysis similar to Rust's**.

## Current state and why it leaks

- **String literals** are safe by design: `lower_string` (apply.rs:1066) emits
  each one as a static `llvm.mlir.global` with a unique symbol from
  `module.strings` (mod.rs:115). Static globals live for the whole program and
  are never freed — correct, since the program text outlives every use.
- **Heap strings** leak: `emit_itostr` (stmt.rs) calls `malloc_call` for a
  12-byte buffer, fills it via `sprintf`, and hands the pointer back to the
  program. Nothing ever calls `free` on it.
- **List cells** leak: `build_cons` (lists.rs:176) mallocs a 16-byte
  `{ head, tail }` cell per cons. Every `map`/`filter`/prelude list leaks.
- The **REPL** is a long-lived process (execute.rs:72, repl.rs) that compiles a
  fresh module per line, so every line's garbage accumulates for the session.

Everything is a first-class `!llvm.ptr`. A string (or list) value can be bound
with `let`, passed as a function argument, stored in a cons cell, captured by a
closure, or returned as `__main`'s value — there is no single point where it is
provably dead, which is exactly why a naive `free` doesn't work.

## Constraints that shape the design

- The language is **pure/immutable**: no assignment, no mutation of an existing
  value, no aliasing-through-mutation. This has a big payoff for refcounting
  (below) and simplifies a lifetime system.
- **HM inference** with generalization at `let`/block-`Decl` boundaries
  (`Polytype::TypeQuantifier`, types.rs:130; `generalise`, types.rs:300).
  Any new type-level sort must ride the existing instantiate/unify machinery.
- Codegen is **monomorphic by construction**: every polymorphic binding is
  specialized per use-site (`specialize_binding`, apply.rs; `default_free_vars`,
  apply.rs:772), producing plain `func.func`s. A whole-program analysis on the
  specialized program is therefore tractable — we do not need Rust's modular
  borrow checking.
- The JIT reads `__main`'s result **after** the function returns
  (execute.rs:91-176), so any value that escapes into the result slot must
  outlive the invocation.

---

## The design space

| Strategy | Reclaims within a run | Compile-time | Cycle-safe | Effort | Verdict |
|---|---|---|---|---|---|
| A. Bump arena + reset per run | Peak-of-run only | No | — | Small | Do now (baseline) |
| B. Reference counting | Yes (live set) | No | **Yes (immutability)** | Medium | Sound default |
| C. Ownership + lifetimes (Rust-like) | Yes + stack alloc | Yes | — | Large | The fun one |
| D. Tracing GC (Boehm) | Yes | No | Yes | Medium | Defer |

### A. Bump arena + reset (short-term fix)

A runtime arena owned by the module:

- `@arena_alloc(n)` replaces raw malloc for runtime-allocated values — at minimum
  `itostr` buffers, ideally `build_cons` cells too.
- `@arena_reset()` frees the whole arena (a linked list of chunks).
- Reset at the top of `@__main` (or from `execute` after the result is copied).

Guarantees zero leaks across REPL lines and after each program; within a run
memory grows to the run's *total* allocation. This is the pragmatic baseline and
the fallback for anything that must escape (see Ripple effects). Build it first
regardless of the fancier work.

### B. Reference counting

Give every runtime-allocated object a header: `{ i32 refcount, ... payload }`.
`@retain(ptr)` increments, `@release(ptr)` decrements and `free`s at 0. Static
literal globals are marked (a sentinel refcount, or a flag in the header) so
`release` skips them.

**The key insight: the language is immutable, so reference-count cycles cannot
form.** A cyclic structure requires mutation of a pointer after creation
(`p.tail = p`), which the language forbids. Refcounting is therefore *complete*:
no cycle collector needed. This makes B the sound, low-complexity choice for
real within-run reclamation.

The compiler inserts `retain`/`release` on:

- `let` bindings and function arguments/returns (ownership transfer = transfer
  without inc/dec; `retain` only on copy/share, e.g. passing the same value to
  two places).
- closure captures (closures.rs) — a captured owned value is owned by the
  closure record.
- cons-cell construction (lists.rs:176) — storing a heap value into a cell
  retains it; the cell releases its payloads when dropped.
- `match` — destructuring moves fields out of the scrutinee; unused/matched
  remainder is dropped.
- builtins — `print`/`println` take a *borrow* (no retain/release); a consuming
  builtin would release its argument after use.

That last bullet is where refcount and lifetimes start to blur: to avoid
retain/release noise you want move semantics, which is a compile-time notion.
So Phase 2 (below) is really a **linearity pass that elides inc/dec on moves**.

### C. Compile-time ownership + lifetimes (the fun one)

Two nested sub-designs:

- **C1 — linear/affine core.** A value is owned by its binding; heap-typed
  values are *move-only* (use at most once unless explicitly copied), scalar
  types are `Copy`. This alone buys sound drop placement (compile-time frees)
  and non-escaping stack allocation. It is a modest extension of HM.
- **C2 — borrows + regions (Rust's system).** Add `&'a T` references so a
  function like `print : &str -> unit` reads without consuming, enabling
  `print s; print s;`. This is the full Rust-flavored feature set: lifetime
  parameters, elision, region inference, and a borrow check that rejects
  use-after-move and borrows outliving their owner.

C2 is the centerpiece of this plan; C1 is its stepping stone.

### D. Tracing GC

A precise collector over the known heap graph would need exact stack maps for
the JIT'd LLVM code (roots), which is heavy. A **conservative collector**
(Boehm GC) linked into the process avoids that: route all allocation through
`GC_malloc`, scan the C/JIT stack conservatively. Work is small, but it's a
third-party dependency, gives no compile-time story, and — arguably — is the
least "fun" option for a teaching compiler. Defer unless B/C disappoint.

---

## Recommended roadmap

1. **Phase 0** — arena + reset (Strategy A). Fix the actual leak today.
2. **Phase 1** — refcounting runtime and a codegen inc/dec pass (Strategy B).
3. **Phase 2** — a linearity/move pass that elides refcount traffic, and
   consuming builtins (C1).
4. **Phase 3** — borrows and a Rust-style lifetime analysis on top (C2),
   replacing refcount traffic with statically placed frees and, for
   non-escaping values, `llvm.alloca` instead of `malloc`.

Phase 0 should land immediately. Phases 1-2 are a sound default that can ship.
Phase 3 is the research/experiment this plan is mostly about.

---

## Phase 0 — Arena

**Runtime** (new `src/codegen/arena.rs` or in `lists.rs`):

- `@arena_alloc(n) -> i64`: keep a linked list of chunks; each chunk has a bump
  cursor; on overflow, `malloc` a fresh chunk and link it. Returns an `i64`
  pointer (same convention as `malloc_call`), `inttoptr`'d by callers.
- `@arena_reset()`: walk the chunk list, `free` each chunk, null the head.
- Emit both as `func.func` bodies (pure MLIR: `arith`, `llvm` gep/load/store,
  `cf`/`scf` control flow) — no C runtime needed. Declare libc `@free(i64) -> ()`
  once (mirror `ensure_printf`, stmt.rs; new `Module::free_declared` flag,
  mod.rs).
- Route allocation through the arena: change `malloc_call` (lists.rs:77) to call
  `@arena_alloc`, and `emit_itostr` (stmt.rs) to use it.

**Reset boundary**:

- Emit `@arena_reset()` as the first op in `@__main`'s entry block (stmt.rs
  `lower`), so every run frees the previous run's arena. REPL lines are fresh
  modules, so a session never accumulates.
- Optionally also reset from `execute` (execute.rs:72) after `invoke_packed`
  returns — by then the result has been copied into Rust `String`/`Vec`s and the
  pointer is no longer needed.

**Tests**: existing suite stays green (allocation addresses are opaque);
programs that previously leaked across REPL lines must now run clean. To make
leakage observable, expose a `@__arena_bytes` helper or a debug counter read by
tests.

**Footprint**: one new file (~120 lines of MLIR emission), one flag, two call
sites. Low risk.

---

## Phase 1 — Reference counting

**Runtime** (new `src/codegen/rc.rs`):

- Object header: `{ i32 refcount, ... payload }`; `@retain(ptr) -> ()`,
  `@release(ptr) -> ()`. `@release` reads the header; a static-literal marker
  (e.g. refcount `-1`) makes it a no-op; at 0 it `free`s the block.
- `itostr` allocates `12 + header` and returns the payload pointer (rc = 1).
  `build_cons` does the same for cells.
- Static globals from `lower_string` are marked `static` so `release` ignores
  them — a heap string can never free a literal.

**Codegen inc/dec pass** (`src/codegen/ownership.rs`):

- A pre-codegen walk decides, per SSA value, whether it *owns* a heap pointer
  and how many times it is *shared*.
- Insert `retain` when a value's ownership is shared (two bindings, a closure
  capture, storage into a cons cell); `release` where a binding ends or a
  matching `match` field is dropped.
- Move = ownership transfer: **no** retain/release emitted.
- Because the language is immutable, no cycle handling is required — this is
  what makes the pass tractable.

**Builtins**: `print`/`println` take a non-owning (borrowed) pointer — no
retain/release at the call site; the value's owner still drops it.

**Tests**: compile a program that builds a big list and a long `itostr` loop,
then assert (via a runtime allocation/deallocation counter exposed as a helper)
that the live count returns to baseline. Regression: every prelude
`map`/`filter`/`foldl` test.

**Footprint**: medium. The runtime is small; the ownership walk touches every
binding/application/match/closure path in codegen.

---

## Phase 2 — Linear / move semantics (C1)

The compile-time backbone that makes Phase 1 efficient and Phase 3 possible:

- Define a **linearity judgment** in `types.rs` (or a new `src/linear.rs`):
  heap-typed values are `Move` (used at most once), scalars are `Copy`. Track
  this in the typing context alongside `Polytype`.
- Reject `use after move`: a second reference to a moved value is a compile
  error (mirror how `algo_w` reports `UnificationError`, types.rs:523).
- Give the language an explicit **copy** for when sharing is wanted (e.g.
  `copy s`), which `retain`s.
- This pass elides most of Phase 1's retain/release: moves are no-ops, only
  `copy` and cons-cell storage retain.

**Footprint**: a new analysis pass over the AST plus a few error messages;
codegen gains a `drop` pass that frees owned values at their last use.

---

## Phase 3 — Borrows and lifetimes (C2, the fun part)

### 3a. A lifetime sort in the type system

- Extend `Monotype` (types.rs:22) with a reference form, e.g.
  `Monotype::Borrow(Lifetime, Box<Monotype>)`, and a `Lifetime` sort
  (`Lifetime::Var(String)` | `Lifetime::Static`).
- Reuse the existing quantification machinery: `Polytype::TypeQuantifier`
  (types.rs:130) gains a counterpart that ranges over lifetimes, so
  `∀'a. &'a str -> unit` is expressible; `instantiate` (types.rs:143) and
  `generalise` (types.rs:300) generalize to fresh lifetime variables exactly as
  they already do for type variables.
- **Subtyping on lifetimes**: `&'a T <: &'b T` when `'a: 'b` (outlives). `unify`
  (types.rs:3) stays for types; lifetimes get their own constraint solving
  (3d).

### 3b. Surface syntax and AST

- Grammar + `ENode` (ast.rs:205): a reference type `&T`, a borrow expression
  `&e` (and optionally a `mut`/unique variant if we want uniqueness-based
  in-place updates later), and `'a` annotations where inference can't elide.
- Default to **elision** like Rust: `print : &str -> unit` means "a borrow with
  an inferred lifetime", so existing programs barely change.

### 3c. Ownership analysis (the borrow checker)

New pass `src/borrow.rs`, run after typecheck on the (still polymorphic) AST —
the language is pure, so ownership is type-independent and one analysis over the
program text suffices:

- Each binding owns its value; `&e` creates a *borrow* of `e` (non-owning).
- A value may be **borrowed immutably many times**, but **moved while borrowed
  is an error** (a borrow must not outlive its owner).
- `match` destructuring moves fields out of the scrutinee; a remaining borrow of
  the scrutinee is an error.
- Closure captures: a closure capturing `&x` is a borrow and constrains the
  closure's lifetime; a closure capturing `x` moves it. This is the hardest
  sub-problem (Rust's closure capture analysis) — see Ripple effects.

### 3d. Region / lifetime inference

- After HM, collect **outlives constraints** (`'a : 'b`) from borrow uses,
  function calls, and return positions; solve with a small union-find / graph
  pass (much simpler than Rust's NLL because the analysis is whole-program, not
  per-crate).
- Assign each owned value a region; the region of `__main`'s return value is
  `'static` (it escapes to the JIT), so its allocation is arena-owned, not
  freed.

### 3e. Codegen: drop placement and stack allocation

With proven lifetimes, codegen no longer needs refcount traffic on the owned
paths:

- **Drop**: emit `free`/`@arena_release` at each owned value's last use
  (computed from the regions).
- **Stack allocation**: if a value's region is contained within one function
  (it never escapes), allocate with `llvm.alloca` in that function instead of
  `malloc` — zero heap traffic, zero frees. This is the payoff that makes
  lifetimes "fun": `print (itostr 42)` becomes an alloca + sprintf, freed
  implicitly by stack unwinding.
- The **specialization bonus**: because codegen already specializes every
  binding per use-site (apply.rs), lifetimes are applied to already-monomorphic
  bodies — no higher-rank lifetime plumbing through the generalizer is needed at
  codegen time.

### 3f. Why this is tractable here (and why it's Rust's hard part)

Rust's borrow checker is modular (public signatures, generics, HRTB, NLL) and
runs before monomorphization. SpicyLang specializes first and analyzes second,
so the checker sees only concrete lifetimes and concrete types. The genuinely
hard remaining piece is **closure captures** (3c) and **higher-order
functions returning borrows** (`filter : (a -> &bool) -> ...`); everything else
is a straightforward region pass over a monomorphic AST.

---

## Ripple effects

- **`__main` result escaping** (execute.rs:91): the JIT reads the return value
  after the function returns, so any owned value returned by the final
  expression must outlive the run. Treat that region as `'static`; the arena
  (Phase 0) owns it, and `execute` may reset the arena after copying the result.
- **Closure capture semantics** (closures.rs): the current closure records hold
  captured values by pointer. Moving vs. borrowing a capture is the biggest
  behavioral change and needs its own design pass.
- **Prelude ergonomics**: `map`, `filter`, `length`, `foldl` should take
  *borrows* of their list argument (`&list a`) so `map f xs` doesn't consume
  `xs`; this is where lifetimes first pay off in user code. Current prelude
  signatures (`builtins-and-prelude.md`) must be revisited.
- **`print`/`println` become borrows**: `print : &str -> unit`. Programs that
  print a literal (static) or a heap string both work; a `let s = itostr 42;
  print s; print s;` becomes legal — the exact case refcounting alone can't
  handle ergonomically.
- **Specialization cache keys**: if a lifetime-annotated function is specialized,
  the cache key (apply.rs) may need to include region info, or lifetimes are
  applied after specialization so keys are unchanged.
- **REPL**: each line re-analyzes the accumulated program; lifetime analysis
  cost is small relative to re-lowering, so no change beyond the usual
  re-run cost.

## Tests and verification

- **Phase 0**: REPL-style repeated execution stays flat (instrument
  `@__arena_bytes`); all existing codegen tests pass unchanged.
- **Phase 1/2**: allocation/deallocation counters show live count returning to
  baseline for `itostr` loops and prelude `map`/`filter`; a counter-triggered
  test that a stored string's refcount hits 1 and drops correctly.
- **Phase 3 (negative)**: `print s; print s;` with `print : str -> unit`
  (owning) errors *use-after-move*; the same with `&str` typechecks.
  Borrow-outlives-owner (`let r = &s; drop s; use r`) rejected.
- **Phase 3 (positive)**: `let s = itostr 42; print s; println s;` compiles to
  stack-alloca + two prints, no malloc; `filter isEven xs` keeps `xs`
  usable afterward.
- **Regression**: the full existing suite — HM, codegen, JIT, prelude tests —
  must pass; the only expected churn is new rejection cases for move/borrow
  violations.

## Estimated footprint

- **Phase 0**: ~1 new file, 1 flag, 2 call sites. Small.
- **Phase 1**: ~1 runtime file + an ownership walk over every codegen path.
  Medium.
- **Phase 2**: a linearity pass (~200-300 lines) + drop placement in codegen.
  Medium.
- **Phase 3**: `Monotype`/`Polytype` extension, grammar + AST, `src/borrow.rs`
  (region inference + borrow check), codegen drop/alloca. **Large — the bulk of
  the project's effort**, and the piece most worth prototyping in isolation
  (a standalone `borrow.rs` over the AST, tested with pure compile-reject cases,
  before any codegen integration).
