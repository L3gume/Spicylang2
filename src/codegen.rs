//! MLIR code generation.
//!
//! Lowers a type-checked [`Program`] into an MLIR module that can be fed to
//! the LLVM backend and JIT-compiled for the REPL.
//!
//! Pipeline: parse -> typecheck -> [this module] -> LLVM backend -> JIT.
//!
//! # Binding
//! Use [melior](https://github.com/ravenscroftj/melior), the Rust bindings
//! over the MLIR C API (`mlir-sys`). To enable it, uncomment the `melior`
//! dependency in `Cargo.toml` and make sure a system LLVM with `llvm-config`
//! and the MLIR libraries is available.
//!
//! # Suggested lowering
//! - Create one `mlir::ir::Context`; register the dialects we emit:
//!   `func`, `arith`, `cf`, `llvm` (and `mlir` for custom enum types).
//! - Top-level `let` bindings become `func.func` symbols with the binding's
//!   generalized type (a function value is just a function symbol).
//! - Each statement is emitted as calls to those symbols from an entry
//!   function `@__main`; the final expression's value becomes `func.return`.
//! - `print` lowers to `llvm.call @printf` on a string operand.
//! - Pattern matches lower to `scf.if` / `cf.br` on the discriminant.
//!
//! Everything below is a skeleton: function signatures and dispatch points
//! are in place, marked `TODO(melior)`. No MLIR is emitted yet.
#![allow(dead_code)] // scaffolds are called once melior is enabled

use crate::ast::{Program, Stmt};
use crate::types::Monotype;

// ----------------------------------------------------------------------------
// Module (top-level MLIR container)
// ----------------------------------------------------------------------------

/// An MLIR module under construction.
///
/// TODO(melior): hold `mlir::ir::Module`, created from an `mlir::ir::Context`
/// that owns dialect registration. Keep the `Context` alive for the whole
/// REPL session so bindings can be appended across input lines.
pub struct Module {
    // context: mlir::ir::Context,
    // module:  mlir::ir::Module,
    functions: usize,
}

impl Module {
    /// Create an empty module.
    pub fn new() -> Module {
        Module { functions: 0 }
    }

    /// Number of top-level `func.func` operations emitted so far.
    pub fn function_count(&self) -> usize {
        self.functions
    }

    /// TODO(melior): print the module in MLIR textual form via
    /// `mlir::ir::Module::to_string()`.
    pub fn dump(&self) -> String {
        String::new()
    }
}

/// Lower a type-checked program to an MLIR module.
///
/// Returns an error string if any statement cannot be lowered (e.g. an AST
/// node with no dialect mapping yet).
pub fn lower(prog: &Program) -> Result<Module, String> {
    let mut module = Module::new();
    for stmt in &prog.stmts {
        lower_stmt(stmt, &mut module)?;
    }
    Ok(module)
}

// ----------------------------------------------------------------------------
// Statements
// ----------------------------------------------------------------------------

fn lower_stmt(stmt: &Stmt, module: &mut Module) -> Result<(), String> {
    // TODO(melior): dispatch on `&*stmt.s`:
    //   SNode::Decl(name, typ, expr) -> declare a `func.func` whose signature is
    //     `lower_type(typ)` and whose body is `lower_expr(expr)`; bump
    //     `module.functions`.
    //   SNode::Expr(expr)            -> append `lower_expr(expr)` to the entry
    //     function body; a top-level expression statement is an effectful call.
    //   SNode::Print(expr)           -> lower `expr`, then `llvm.call @printf`.
    //   SNode::TypeDecl(header, dec) -> register the enum/alias; enums become
    //     `mlir` custom types or `i32` discriminants plus variant layout.
    let _ = (stmt, module);
    Ok(())
}

// ----------------------------------------------------------------------------
// Expressions
// ----------------------------------------------------------------------------

/// TODO(melior): lower `expr` to MLIR ops inside the current function body.
///
/// Pointer map (ENode variant -> dialect ops):
///   Variable(name)          -> `func.call` the symbol / `func` block argument
///   Literal(Int)            -> `arith.constant` i32
///   Literal(Float)          -> `arith.constant` f32
///   Literal(Bool)           -> `arith.constant` i1
///   Literal(Str)            -> a `llvm.mlir.global` string + `llvm.getelementptr`
///   Abstraction(binding, e) -> `func.func` with the binding's type; body =
///                              `lower_expr(e)`
///   Application(f, x)       -> `func.call` / `func.call_indirect`
///   Let(n, e1, e2)          -> `scf.for`-free: hoist as a `func.func` + call,
///                              or use SSA value + `arith` if inlined
///   IfElse(c, t, e)         -> `scf.if` (or `cf.cond_br`)
///   Block(stmts, e)         -> emit statements into a nested region, return `e`
///   Comparison(..)          -> `arith.cmpi` / `arith.cmpf`
///   Arithmetic(..)          -> `arith.addi/subi/muli/...` or `arith.addf/...`
///   Logical(..)             -> `arith.andi/ori/xori`
///   Unary(..)               -> `arith.subi` / `arith.xori` (i1 not)
///   List(es)                -> heap-allocate via `llvm` malloc, or a struct
///                              header + element buffer
///   Cons(h, t)              -> prepend to a list header struct
///   Match(scrut, cases)     -> `scf.if` chain on the discriminant
fn lower_expr(_expr: &crate::ast::Expr) -> Result<(), String> {
    Err("codegen: expression lowering not implemented".to_string())
}

// ----------------------------------------------------------------------------
// Types
// ----------------------------------------------------------------------------

/// TODO(melior): map a [`Monotype`] to an `mlir::ir::Type`.
///
/// Suggested mapping:
///   int              -> i32  (`IntegerType::get(ctx, 32)`)
///   float            -> f32
///   bool             -> i1
///   str              -> `llvm.ptr<f8>` (LLVM `i8*`)
///   unit             -> i32 (placeholder; there is no MLIR empty type)
///   list T           -> `llvm.ptr` to a list header { len: i64, cap: i64, data: ptr<T> }
///   T1 => T2         -> `FunctionType([T1], [T2])` (or `llvm.ptr` function pointer)
///   enum E           -> i32 discriminant (with variant payloads as structs)
///   E t1 ... tn      -> struct { disc: i32, fields: (t1, ..., tn) }
fn lower_type(_typ: &Monotype) -> Result<(), String> {
    Err("codegen: type lowering not implemented".to_string())
}

// ----------------------------------------------------------------------------
// JIT execution (for the REPL)
// ----------------------------------------------------------------------------

/// Run a compiled module through the LLVM JIT and return its exit value.
///
/// TODO(melior): build an `mlir::ExecutionEngine` from `module` (linking
/// `mlir_runner_utils` and any custom runtime helpers), then invoke the
/// `@__main` function packed with the top-level arguments.
///
/// For the REPL, keep the `Context`/`Module` alive across input lines and
/// re-run the JIT on every statement; global bindings persist because the
/// generated symbols accumulate in the module.
pub fn execute(_module: &Module) -> Result<i64, String> {
    Err("codegen: jit execution not implemented".to_string())
}
