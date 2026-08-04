use crate::ast::*;
use crate::grammar;
use std::sync::OnceLock;

static PRELUDE : OnceLock<Vec<Stmt>> = OnceLock::new();

pub fn get_prelude() -> &'static Vec<Stmt> {
    PRELUDE.get_or_init(|| {
        let buf = include_str!("prelude/prelude.spcy");
        match grammar::ProgParser::new().parse(buf).map_err(|e| format!("{}", e)) {
            Ok(prog) => prog.stmts,
            _ => vec![]
        }
    })
}
