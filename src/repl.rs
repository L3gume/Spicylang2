//! Interactive read-eval-print loop.

use crate::ast;
use crate::codegen;
use crate::display::render_type;
use crate::types;
use std::io::{self, Write};
use std::process;

pub fn repl_loop(initial: Option<Box<ast::Program>>) {
    let mlir_ctx = codegen::new_context();
    let stdin = io::stdin();
    let mut buffer = String::new();

    let mut accumulated_stmts: Vec<ast::Stmt> = match &initial {
        Some(prog) => prog.stmts.clone(),
        None => Vec::new(),
    };

    loop {
        print!("> ");
        io::stdout().flush().unwrap();

        buffer.clear();
        match stdin.read_line(&mut buffer) {
            Ok(0) => break,
            Ok(_) => {},
            Err(e) => {
                eprintln!("read error: {}", e);
                process::exit(1);
            }
        }

        let trimmed = buffer.trim();
        if trimmed.is_empty() || trimmed == "exit" {
            if trimmed == "exit" { break; }
            continue;
        }

        match ast::Program::parse(trimmed) {
            Err(e) => eprintln!("parse error: {}", e),
            Ok(new_prog) => {
                let new_count = new_prog.stmts.len();
                accumulated_stmts.extend(new_prog.stmts);

                let mut full = Box::new(ast::Program {
                    stmts: accumulated_stmts.clone(),
                    ctx: types::TypeContext::new(),
                });

                match ast::Program::typecheck(&mut full) {
                    Err(e) => {
                        eprintln!("type error: {}", e);
                        accumulated_stmts.truncate(accumulated_stmts.len() - new_count);
                    }
                    Ok(()) => {
                        accumulated_stmts = full.stmts.clone();
                        // Determine the last statement's type and, for a
                        // `let`, which nullary binding to invoke to read its
                        // value back.
                        let (last_type, last_kind, target) = match full.stmts.last() {
                            Some(stmt) => match &*stmt.s {
                                ast::SNode::Expr(e) => (Some(e.typ.clone()), LastKind::Expr, None),
                                ast::SNode::Decl(e1, _, e2) => {
                                    let is_fn = matches!(&e2.typ, types::Monotype::TypeFuncApplication(f, _) if matches!(**f, types::TypeFunc::Fn));
                                    if is_fn {
                                        (Some(e2.typ.clone()), LastKind::DeclFn, None)
                                    } else {
                                        let name = match &*e1.e {
                                            ast::ENode::Variable(n) => n.clone(),
                                            _ => String::new(),
                                        };
                                        let target = if name.is_empty() {
                                            None
                                        } else {
                                            Some((name, e2.typ.clone()))
                                        };
                                        (Some(e2.typ.clone()), LastKind::DeclScalar, target)
                                    }
                                }
                                _ => (None, LastKind::Other, None),
                            },
                            None => (None, LastKind::Other, None),
                        };
                        match codegen::lower(&full, &mlir_ctx) {
                            Err(e) => eprintln!("codegen error: {}", e),
                            Ok(mut module) => {
                                if matches!(last_kind, LastKind::DeclFn) {
                                    match last_type {
                                        Some(typ) => println!("  : {} : <fn>", render_type(&typ)),
                                        None => println!("  : <fn>"),
                                    }
                                    continue;
                                }
                                match codegen::execute(&mut module, target) {
                                    Err(e) => eprintln!("execution error: {}", e),
                                    Ok(result) => {
                                        match last_type {
                                            Some(typ) => println!("  : {} = {:?}", render_type(&typ), result),
                                            None => println!("  = {:?}", result),
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
enum LastKind {
    Expr,
    DeclFn,
    DeclScalar,
    Other,
}
