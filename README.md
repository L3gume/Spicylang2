<div align="center">

<img src="resources/MerlinLogo.png" alt="Merlin logo" width="200" />

# Merlin

A statically-typed functional programming language compiled to native code via MLIR and LLVM.

</div>

Merlin is a small ML-family language with **Hindley–Milner type inference**,
algebraic data types, records, pattern matching, and a JIT-compiled REPL. It is
implemented in Rust and lowers to LLVM through [MLIR](https://mlir.llvm.org/)
using the [Melior](https://github.com/edg-l/melior) bindings.

This is a toy project mean to learn about languages and compilers,
not a serious language that is meant for production. If you really want
to contribute or chat then please reach out but I have no ambition of creating
the next mainstream language, you'd be better off with OCaml.

## Features

- **Static typing with full type inference** — no annotations required, inferred
  via Algorithm-W (`docs/typerules.md` documents the rules).
- **Algebraic data types** — user-defined `enum`s and `type` aliases with
  parametric polymorphism (`Option('a)`, `Result('a, 'err)`).
- **Records** — construction, field access, pattern matching, and functional
  updates (`with`).
- **Pattern matching** — with exhaustiveness checking over literals, constructors,
  lists, and records.
- **First-class functions** — closures, currying, and recursive `let` bindings.
- **Lists** — built-in cons (`::`) and list literals, plus a standard `prelude`
  of `map`, `filter`, `fold`, and friends.
- **Native compilation** — lowers to MLIR, then to an object file and executable.
- **JIT-compiled REPL** — evaluate expressions interactively with the same
  compiler backend.
- **Tail-call optimization** — self tail calls lower to loop backedges.

## Example

```mlir
enum Option('a) =
    Some('a)
    | None;

record Foo =
    {
        bar : int,
        baz : Option str
    };

let describe = \foo => match foo
    | Foo { bar: 69, baz: _ } => "nice!"
    | Foo { bar: n, baz: maybe_str } => (
        match maybe_str
        | Some s => s
        | None => "None str"
    );

let x1 = Foo { bar: 69, baz: Some "420" };
let x2 = Foo { bar: 420, baz: None };

println (describe x1);
println (describe (x1 with { bar: 420 }));
println (describe x2);
```

```mlir
let fib = \(n : int) => match n
    | 0 => 1
    | 1 => 1
    | x => fib (x - 1) + fib (x - 2);

let tl_fib = \(n : int) =>
    let loop = \i a b =>
        if i == n then a else loop (i + 1) b (a + b)
    in loop 0 1 1;

println (itostr (tl_fib 40));
```

More examples live in [`programs/`](programs/).

## Building

Merlin requires a Rust toolchain plus a system LLVM/MLIR (with `llvm-config`).
MLIR support is behind the `melior` dependency in `Cargo.toml`.

```sh
cargo build --release
```

## Usage

Compile and run a program:

```sh
cargo run -- programs/fib.mln
```

This parses, typechecks, lowers to MLIR, and links a native executable named
after the source file.

Launch the REPL (optionally with a program's bindings already in scope):

```sh
cargo run                    # bare REPL
cargo run -- programs/list.mln --repl
```

Command-line flags:

| Flag        | Description                                          |
|-------------|------------------------------------------------------|
| `--ast`     | Dump the parsed AST before typechecking              |
| `--mlir`    | Dump the generated MLIR module                       |
| `--repl`    | Start the REPL after loading the program             |
| `--prelude` | Load the standard prelude (for REPL sessions)        |

## Language overview

### Built-in types

`int`, `float`, `bool`, `str`, `char`, `()` (unit), and `list T`.

### Declarations

```mlir
type Name = int;                       # type alias
enum Option('a) = Some('a) | None;     # enum
record Person = { name : str, age : int };
```

### Expressions

```mlir
let add = \x y => x + y;               # lambdas (multiple binders curried)
let inc = \(x : int) => x + 1;         # optional type annotations
let result = let x = 5 in x * x;       # let ... in
let xs = 1 :: 2 :: 3 :: [];            # cons + list literals

match xs
| [] => "empty"
| x :: rest => itostr x;               # pattern matching
```

### Built-in functions

`print`, `println`, `itostr`, `ftostr`, `btostr`, `strtoi`, `strtof`,
`strtob`, `itof`, `ftoi`, and `readin` are provided by the compiler.

### Prelude

The [`prelude`](src/prelude/prelude.mln) defines `Option`/`Result` plus list
utilities: `head`, `tail`, `last`, `len`, `iter`, `map`, `fold` (`lfold`/
`rfold`), `rev`, `filter`, `contains`, `find`, `append`, and more.

## Project structure

```
src/
  grammar.lalrpop    # parser (LALRPOP)
  ast.rs             # AST and display
  types.rs           # Hindley–Milner type inference (Algorithm-W)
  codegen/           # MLIR/LLVM lowering (expressions, lists, records, ...)
  prelude/           # prelude written in Merlin itself
  repl.rs            # JIT-compiled REPL
docs/                # grammar, typing rules, and design notes
plans/               # in-progress design documents
programs/            # example programs
tests/               # parser, typechecker, codegen tests
```

## Status

Merlin is an active work in progress and not a serious project. See [`TODO.md`](TODO.md) for the roadmap
and [`bugs.md`](bugs.md) for known issues. In particular, records are currently
*nominal*; [`docs/rowtypes.md`](docs/rowtypes.md) describes a planned migration
to structural row-polymorphic records.
