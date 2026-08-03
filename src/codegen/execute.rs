//! JIT execution (for the REPL).

use super::Module;

/// Run a compiled module through the LLVM JIT and return its exit value.
///
/// TODO(melior): build an `mlir::ExecutionEngine` from `module` (linking
/// `mlir_runner_utils` and any custom runtime helpers), then invoke the
/// `@__main` function packed with the top-level arguments.
///
/// For the REPL, keep the `Context`/`Module` alive across input lines and
/// re-run the JIT on every statement; global bindings persist because the
/// generated symbols accumulate in the module.
#[allow(dead_code)] // TODO: JIT stub
pub fn execute(_module: &Module) -> Result<i64, String> {
    Err("codegen: jit execution not implemented".to_string())
}
