//! Spicylang compiler library.

pub mod ast;
pub mod codegen;
pub mod display;
pub mod prelude;
pub mod repl;
pub mod types;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar);
