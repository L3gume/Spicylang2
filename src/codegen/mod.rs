//! MLIR code generation.
//!
//! Lowers a type-checked [`Program`] into an MLIR module that can be fed to
//! the LLVM backend and JIT-compiled for the REPL.
//!
//! Pipeline: parse -> typecheck -> [this module] -> LLVM backend -> JIT.
//!
//! Layout:
//! - [`Module`], the type registries, and the shared environment live here.
//! - [`stmt`] lowers top-level statements and declarations.
//! - [`expr`] lowers expressions.
//! - [`closures`], [`lists`], [`enums`], [`types`] provide the pieces those
//!   use (closure conversion, cons cells, tagged enum values, type mapping).
//! - [`execute`] runs the compiled module through the JIT.

mod apply;
mod closures;
mod enums;
mod execute;
mod expr;
mod lists;
mod stmt;
mod types;

pub use execute::{ExecutionResult, execute};
pub use stmt::lower;

use crate::ast::*;
use crate::types::Monotype;
use melior::ir::{
    r#type::FunctionType,
    Value,
};
use std::collections::HashMap;

/// A binding in the current expression scope.
#[derive(Clone)]
pub enum EnvEntry<'c, 'a> {
    /// A lowered SSA value (e.g. `let x = 42 in ...`).
    Value(Value<'c, 'a>),
    /// A lambda registered in [`Module::abstractions`]; specialized on demand
    /// at each use (e.g. `let x = \y => y in ...`).
    Abstraction(String),
}

pub(crate) type Env<'c, 'a> = HashMap<String, EnvEntry<'c, 'a>>;

// ----------------------------------------------------------------------------
// Context
// ----------------------------------------------------------------------------

/// Create an MLIR context with all dialects registered.
///
/// `arith.constant` (and every other op we emit) fails to verify unless its
/// dialect is loaded into the context. The REPL owns one such context for the
/// whole session and reuses it across input lines.
pub fn new_context() -> melior::Context {
    let registry = melior::dialect::DialectRegistry::new();
    melior::utility::register_all_dialects(&registry);
    let context = melior::Context::new();
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    melior::utility::register_all_llvm_translations(&context);
    context
}

// ----------------------------------------------------------------------------
// Module (top-level MLIR container)
// ----------------------------------------------------------------------------

/// Layout of a declared enum: its variants and their payload field types.
///
/// A parametric enum's field types may reference the header's type variables
/// (e.g. `enum option a = None | Some(a)`); those are resolved when the enum
/// is *applied* in `lower_type`.
pub struct EnumLayout {
    /// The header's type parameter names (e.g. `a` in `option a`).
    pub params: Vec<String>,
    /// `(variant name, payload field types)` in declaration order.
    pub variants: Vec<(String, Vec<Monotype>)>,
}

/// A polymorphic (or monomorphic) lambda binding `name = \p => body`, kept so
/// a specialized `func.func` can be emitted on demand for every concrete type
/// the binding is used at.
pub struct AbstractionInfo {
    /// The bound parameter name.
    pub param: String,
    /// The declared parameter type (may be `infer`).
    #[allow(dead_code)] // informational
    pub param_type: Monotype,
    /// The body expression (owned clone).
    pub body: Expr,
    /// The abstraction's resolved type, used to compute the substitution
    /// that specializes the body for a concrete instantiation.
    pub abs_type: Monotype,
}

/// An MLIR module under construction.
///
/// TODO(melior): hold `melior::ir::Module`, created from a `melior::Context`
/// that owns dialect registration. Keep the `Context` alive for the whole
/// REPL session so bindings can be appended across input lines.
pub struct Module<'a> {
    context: &'a melior::Context,
    module:  melior::ir::Module<'a>,
    functions: usize,
    /// Declared enum layouts, keyed by type name.
    enums: HashMap<String, EnumLayout>,
    /// Declared type aliases, keyed by alias name; the value is the expanded
    /// right-hand side, which may reference the header's type variables.
    aliases: HashMap<String, Monotype>,
    /// Number of string globals emitted, for unique symbol names.
    strings: usize,
    /// Whether the external `printf` declaration has been emitted.
    printf_declared: bool,
    /// Whether the external `malloc` declaration has been emitted.
    malloc_declared: bool,
    /// Types of the top-level `func.func` symbols, keyed by name; a
    /// `Variable` that is not a bound parameter lowers to `func.call` on it.
    symbols: HashMap<String, FunctionType<'a>>,
    /// Number of closures emitted, for unique symbol names.
    closures: usize,
    /// Lambda bindings awaiting per-type specialization, keyed by name.
    abstractions: HashMap<String, AbstractionInfo>,
    /// Cache of emitted specializations: `(binding name, canonical
    /// instantiation type) -> closure symbol`.
    specializations: HashMap<(String, String), String>,
    /// Cache of emitted partial applications: `(binding name, argument
    /// fingerprint, instantiation type) -> partial function symbol`. Keyed by
    /// the argument so recursive partial applications (e.g. `map fn xs` inside
    /// `map`) reuse the same function instead of re-lowering infinitely.
    partials: HashMap<(String, String, String), String>,
    /// Number of specialization symbols emitted.
    spec_counter: usize,
    /// Number of let-bound abstractions registered, for unique registry names.
    let_counter: usize,
    /// Enum constructors: constructor name → `(enum name, variant index,
    /// arity)`. Built when an enum is declared.
    constructors: HashMap<String, (String, usize, usize)>,
    /// The resolved Spicylang type of the `@__main` entry function's return
    /// value, used by the JIT to interpret the result slot.
    entry_return_monotype: Option<Monotype>,
}

impl<'a> Module<'a> {
    /// Create an empty module inside `context`.
    pub fn new(context: &'a melior::Context) -> Module<'a> {
        Module {
            context,
            module: melior::ir::Module::new(melior::ir::Location::unknown(context)),
            functions: 0,
            enums: HashMap::new(),
            aliases: HashMap::new(),
            strings: 0,
            printf_declared: false,
            malloc_declared: false,
            symbols: HashMap::new(),
            closures: 0,
            abstractions: HashMap::new(),
            specializations: HashMap::new(),
            partials: HashMap::new(),
            spec_counter: 0,
            let_counter: 0,
            constructors: HashMap::new(),
            entry_return_monotype: None,
        }
    }

    /// Number of top-level `func.func` operations emitted so far.
    pub fn function_count(&self) -> usize {
        self.functions
    }

    /// Print the module in MLIR textual form.
    pub fn dump(&self) -> String {
        self.module.as_operation().to_string()
    }

    /// Mutable access to the inner MLIR module (for running passes).
    pub fn as_mlir_module_mut(&mut self) -> &mut melior::ir::Module<'a> {
        &mut self.module
    }

    /// The resolved Spicylang type of the entry function's return value, if
    /// any. `None` means the entry function returns unit.
    pub fn entry_return_monotype(&self) -> Option<&Monotype> {
        self.entry_return_monotype.as_ref()
    }
}