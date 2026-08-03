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
    let mut dump_mlir = false;
    let mut start_repl = false;
    let mut file: Option<String> = None;

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--ast" => dump_ast = true,
            "--mlir" => dump_mlir = true,
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
        None => repl_loop(None),
        Some(path) => {
            let source = match std::fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("error: failed to read `{}`: {}", path, e);
                    process::exit(1);
                }
            };

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

            if let Err(e) = Program::typecheck(&mut prog) {
                eprintln!("typecheck: error: {}", e);
                process::exit(2);
            }
            println!("typecheck: ok");

            let context = codegen::new_context();
            match codegen::lower(&prog, &context) {
                Ok(module) => {
                    println!(
                        "codegen: ok ({} top-level functions)",
                        module.function_count()
                    );
                    if dump_mlir {
                        println!("{}", module.dump());
                    }
                },
                Err(e) => {
                    eprintln!("codegen: error: {}", e);
                    process::exit(3);
                }
            }

            if dump_ast {
                println!("{:#?}", *prog);
            }

            if start_repl {
                repl_loop(Some(prog));
            }
        }
    }
}

fn repl_loop(initial: Option<Box<Program>>) {
    let mlir_ctx = codegen::new_context();
    let stdin = io::stdin();
    let mut buffer = String::new();

    let mut accumulated_stmts: Vec<ast::Stmt> = match &initial {
        Some(prog) => prog.stmts.clone(),
        None => Vec::new(),
    };
    let mut ctx: types::TypeContext = match &initial {
        Some(prog) => prog.ctx.clone(),
        None => types::TypeContext::new(),
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

        match Program::parse(trimmed) {
            Err(e) => eprintln!("parse error: {}", e),
            Ok(new_prog) => {
                let new_count = new_prog.stmts.len();
                accumulated_stmts.extend(new_prog.stmts);

                let mut full = Box::new(ast::Program {
                    stmts: accumulated_stmts.clone(),
                    ctx: types::TypeContext::new(),
                });

                match Program::typecheck(&mut full) {
                    Err(e) => {
                        eprintln!("type error: {}", e);
                        accumulated_stmts.truncate(accumulated_stmts.len() - new_count);
                    }
                    Ok(()) => {
                        ctx = full.ctx.clone();
                        accumulated_stmts = full.stmts.clone();
                        match codegen::lower(&full, &mlir_ctx) {
                            Err(e) => eprintln!("codegen error: {}", e),
                            Ok(mut module) => {
                                match codegen::execute(&mut module) {
                                    Err(e) => eprintln!("execution error: {}", e),
                                    Ok(result) => println!("  = {:?}", result),
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
