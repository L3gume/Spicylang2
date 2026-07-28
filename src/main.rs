use std::io::{self, Write};
use std::process;
use lalrpop_util::lalrpop_mod;
use ast::Program;

mod ast;
mod types;

lalrpop_mod!(pub grammar);

fn main() {
    let mut ctx = types::TypeContext::new();
    let mut buffer = String::new();
    let stdin = io::stdin();

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

        match Program::parse(trimmed) {
            Err(e) => eprintln!("parse error: {}", e),
            Ok(mut prog) => {
                for stmt in prog.stmts.iter_mut() {
                    match stmt.typecheck(&ctx) {
                        Ok((sub, typ)) => {
                            ctx = stmt.ctx.clone();
                            let resolved = typ.apply(&sub);
                            println!("  : {:?}", resolved);
                        },
                        Err(e) => eprintln!("type error: {}", e),
                    }
                }
            }
        }
    }
}

