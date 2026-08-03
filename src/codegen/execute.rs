//! JIT execution (for the REPL).

use crate::types::{Monotype, TypeFunc};
use super::Module;
use super::apply::default_free_vars;
use melior::{ExecutionEngine, pass};

pub enum ExecutionResult {
    Int(i32),
    Float(f32),
    Bool(bool),
    String(String),
    Unit,
}

impl std::fmt::Debug for ExecutionResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecutionResult::Int(n) => write!(f, "{}", n),
            ExecutionResult::Float(n) => write!(f, "{}", n),
            ExecutionResult::Bool(b) => write!(f, "{}", b),
            ExecutionResult::String(s) => write!(f, "\"{}\"", s),
            ExecutionResult::Unit => write!(f, "()"),
        }
    }
}

pub fn execute(module: &mut Module) -> Result<ExecutionResult, String> {
    let context = module.context;

    let pass_manager = pass::PassManager::new(context);
    pass_manager.add_pass(pass::conversion::create_scf_to_control_flow());
    pass_manager.add_pass(pass::conversion::create_arith_to_llvm());
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());
    pass_manager
        .run(module.as_mlir_module_mut())
        .map_err(|e| format!("codegen: pass manager failed: {}", e))?;

    let engine = ExecutionEngine::new(module.as_mlir_module_mut(), 2, &[], false, false);

    let return_type = module.entry_return_monotype().cloned();
    match return_type {
        None => {
            unsafe {
                engine
                    .invoke_packed("__main", &mut [])
                    .map_err(|e| format!("codegen: jit invocation failed: {}", e))?;
            }
            Ok(ExecutionResult::Unit)
        }
        Some(ref mono) => match default_free_vars(mono) {
            Monotype::TypeFuncApplication(ref f, ref args) if args.is_empty() => match **f {
                TypeFunc::Int => {
                    let mut result: i32 = 0;
                    unsafe {
                        engine
                            .invoke_packed(
                                "__main",
                                &mut [&mut result as *mut i32 as *mut ()],
                            )
                            .map_err(|e| format!("codegen: jit invocation failed: {}", e))?;
                    }
                    Ok(ExecutionResult::Int(result))
                }
                TypeFunc::Float => {
                    let mut result: f32 = 0.0;
                    unsafe {
                        engine
                            .invoke_packed(
                                "__main",
                                &mut [&mut result as *mut f32 as *mut ()],
                            )
                            .map_err(|e| format!("codegen: jit invocation failed: {}", e))?;
                    }
                    Ok(ExecutionResult::Float(result))
                }
                TypeFunc::Bool => {
                    let mut result: u8 = 0;
                    unsafe {
                        engine
                            .invoke_packed(
                                "__main",
                                &mut [&mut result as *mut u8 as *mut ()],
                            )
                            .map_err(|e| format!("codegen: jit invocation failed: {}", e))?;
                    }
                    Ok(ExecutionResult::Bool(result != 0))
                }
                TypeFunc::Str => {
                    let mut result: *const std::ffi::c_char = std::ptr::null();
                    unsafe {
                        engine
                            .invoke_packed(
                                "__main",
                                &mut [&mut result as *mut *const std::ffi::c_char as *mut ()],
                            )
                            .map_err(|e| format!("codegen: jit invocation failed: {}", e))?;
                        let s = if result.is_null() {
                            String::new()
                        } else {
                            std::ffi::CStr::from_ptr(result)
                                .to_string_lossy()
                                .into_owned()
                        };
                        Ok(ExecutionResult::String(s))
                    }
                }
                TypeFunc::Unit => {
                    unsafe {
                        engine
                            .invoke_packed("__main", &mut [])
                            .map_err(|e| format!("codegen: jit invocation failed: {}", e))?;
                    }
                    Ok(ExecutionResult::Unit)
                }
                _ => Err(format!("codegen: cannot JIT-execute type {:?}", mono)),
            },
            _ => Err(format!("codegen: cannot JIT-execute type {:?}", mono)),
        },
    }
}
