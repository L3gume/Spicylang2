use std::io::{self, Write};
use std::process;
use lalrpop_util::lalrpop_mod;
use ast::Program;

mod ast;
mod codegen;
mod types;

lalrpop_mod!(pub grammar);

fn main() {
    let mut dump_ast = false;
    let mut start_repl = false;
    let mut file: Option<String> = None;

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--ast" => dump_ast = true,
            "--repl" => start_repl = true,
            "--help" | "-h" => {
                println!("usage: spicylang [--ast] [--repl] <file.spcy>");
                println!("  --ast    dump the program's AST after it completes");
                println!("  --repl   start the REPL with the program already in the context");
                return;
            }
            s if s.starts_with('-') => {
                eprintln!("error: unknown option `{}`", s);
                eprintln!("usage: spicylang [--ast] [--repl] <file.spcy>");
                process::exit(1);
            }
            s => file = Some(s.to_string()),
        }
    }

    match file {
        // No program given: start the REPL with an empty context.
        None => repl_loop(types::TypeContext::new()),
        Some(path) => {
            let source = match std::fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("error: failed to read `{}`: {}", path, e);
                    process::exit(1);
                }
            };

            // Step 1: parse
            let mut prog = match Program::parse(&source) {
                Ok(p) => {
                    println!("parse: ok");
                    p
                }
                Err(e) => {
                    eprintln!("parse: error: {}", e);
                    process::exit(1);
                }
            };

            // Step 2: typecheck
            if let Err(e) = Program::typecheck(&mut prog) {
                eprintln!("typecheck: error: {}", e);
                process::exit(2);
            }
            println!("typecheck: ok");

            // Step 3: codegen (MLIR). TODO: feed the module to the LLVM backend
            // and JIT-compile it once codegen::lower is implemented.
            match codegen::lower(&prog) {
                Ok(module) => println!(
                    "codegen: ok ({} top-level functions)",
                    module.function_count()
                ),
                Err(e) => {
                    eprintln!("codegen: error: {}", e);
                    process::exit(3);
                }
            }

            if dump_ast {
                println!("{:#?}", *prog);
            }

            if start_repl {
                repl_loop(prog.ctx.clone());
            }
        }
    }
}

fn repl_loop(mut ctx: types::TypeContext) {
    let stdin = io::stdin();
    let mut buffer = String::new();

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
                    // TODO(mlir): JIT-compile the statement instead of only
                    // typechecking: codegen::lower on `stmt`, then
                    // codegen::execute with melior's `ExecutionEngine`
                    // (keep the Module alive across lines so bindings persist).
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
