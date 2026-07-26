use lalrpop_util::lalrpop_mod;
use ast::Program;

mod ast;
mod types;

lalrpop_mod!(pub grammar);

fn main() {

    // TODO: Read from args
    // TODO: REPL loop
    // TODO: Read from file
    let prog = r#"
        let eval : int => bool = \(x : int) => \(cond : int => bool) => if cond x then true else false;
        let val = let c = \x => true in eval 69 c;
    "#;
    if let Ok(ast6) = Program::parse(prog) {
        println!("{:?}", *ast6);
    }

}

