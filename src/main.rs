use lalrpop_util::lalrpop_mod;

mod ast;
mod types;

lalrpop_mod!(pub grammar);

#[test]
fn lamba() {
    assert!(grammar::ExprParser::new().parse("x").is_ok());
    assert!(grammar::ExprParser::new().parse("\\x => x").is_ok());
    assert!(grammar::ExprParser::new().parse("x x").is_ok());
    assert!(grammar::ExprParser::new().parse("\\x => x y").is_ok());
    assert!(grammar::ExprParser::new().parse("(\\x => x) y").is_ok());
}

#[test]
fn substitution() {
    // TODO: validate substitutions and applications
}

fn main() {

    // TODO: Read from args
    // TODO: REPL loop
    // TODO: Read from file
    let prog = r#"
        let eval : int => bool = \(x : int) => \(cond : int => bool) => if cond x then true else false;
        let val = let c = \x => true in eval 69 c;
    "#;
    let ast6 = grammar::ProgParser::new().parse(prog);
    println!("{:?}", ast6.unwrap());

}

