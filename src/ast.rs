use crate::{ast::Expr::Variable, types::*, grammar};

#[derive(Debug, PartialEq)]
pub enum Lit {
    Int(i32),
    Float(f32),
    Bool(bool),
    Str(String),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub t: Monotype
}

#[derive(Debug, PartialEq)]
pub struct Binding(pub String, pub Box<Type>);

#[derive(Debug, PartialEq)]
pub enum Stmt {
    Decl(Box<Expr>, Box<Type>, Box<Expr>),  // let x [: Type] = e;
    Expr(Box<Expr>),                        // e; special case, not always ()
    Print(Box<Expr>),                       // print e;
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Variable(String),
    Literal(Box<Lit>),
    Abstraction(Box<Binding>, Box<Expr>),
    Application(Box<Expr>, Box<Expr>),
    Let(String,Box<Expr>,Box<Expr>),
    IfElse(Box<Expr>,Box<Expr>,Box<Expr>),
}

#[derive(Debug)]
pub enum CompOp {
    Eq,
    Less,
    Greater,
    LessEq,
    GreatEq,
}

#[derive(Debug)]
pub enum ArithOp {
    Plus,
    Minus,
    Div,
    Times,
    Mod,
}

#[derive(Debug)]
pub struct Program {
    pub stmts : Vec<Stmt>
}

impl Program {
    pub fn parse(buf : &str) -> Result<Box<Program>, String> {
        grammar::ProgParser::new().parse(buf).map_err(|e| format!("{}", e))
    }

    pub fn typecheck() {
        let mut ctx = TypeContext::new();
        let res = algo_w(&mut ctx, &Box::new(Variable(String::new())));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> Box<Program> {
        Program::parse(src).unwrap()
    }

    fn mono(t: Monotype) -> Box<Type> {
        Box::new(Type { t })
    }

    fn first(p: &Program) -> &Stmt {
        &p.stmts[0]
    }

    // ---- Literals ----

    #[test]
    fn int_literal() {
        let p = parse("42;");
        assert_eq!(p.stmts.len(), 1);
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Int(42))))));
    }

    #[test]
    fn negative_int_literal() {
        let p = parse("-7;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Int(-7))))));
    }

    #[test]
    fn float_literal() {
        let p = parse("3.14;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Float(std::f32::consts::PI))))));
    }

    #[test]
    fn negative_float_literal() {
        let p = parse("-2.5;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Float(-2.5))))));
    }

    #[test]
    fn bool_true_literal() {
        let p = parse("true;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Bool(true))))));
    }

    #[test]
    fn bool_false_literal() {
        let p = parse("false;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Bool(false))))));
    }

    #[test]
    fn string_literal() {
        let p = parse(r#""hello";"#);
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Str("hello".to_string()))))));
    }

    #[test]
    fn empty_string_literal() {
        let p = parse(r#""";"#);
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Str("".to_string()))))));
    }

    #[test]
    fn unit_literal() {
        let p = parse("();");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Unit)))));
    }

    // ---- Variables ----

    #[test]
    fn simple_variable() {
        let p = parse("x;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Variable("x".to_string()))));
    }

    #[test]
    fn underscore_variable() {
        let p = parse("_foo;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Variable("_foo".to_string()))));
    }

    #[test]
    fn alphanumeric_variable() {
        let p = parse("x2y;");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Variable("x2y".to_string()))));
    }

    // ---- Application ----

    #[test]
    fn single_application() {
        let p = parse("f x;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Application(
                Box::new(Expr::Variable("f".to_string())),
                Box::new(Expr::Variable("x".to_string())),
            )))
        );
    }

    #[test]
    fn left_associative_application() {
        let p = parse("f x y;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Application(
                Box::new(Expr::Application(
                    Box::new(Expr::Variable("f".to_string())),
                    Box::new(Expr::Variable("x".to_string())),
                )),
                Box::new(Expr::Variable("y".to_string())),
            )))
        );
    }

    #[test]
    fn application_with_literal_arg() {
        let p = parse("f 42;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Application(
                Box::new(Expr::Variable("f".to_string())),
                Box::new(Expr::Literal(Box::new(Lit::Int(42)))),
            )))
        );
    }

    #[test]
    fn application_with_parenthesized_expr() {
        let p = parse("f (g x);");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Application(
                Box::new(Expr::Variable("f".to_string())),
                Box::new(Expr::Application(
                    Box::new(Expr::Variable("g".to_string())),
                    Box::new(Expr::Variable("x".to_string())),
                )),
            )))
        );
    }

    // ---- Abstraction ----

    #[test]
    fn lambda_without_type_annotation() {
        let p = parse("\\x => x;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                Box::new(Expr::Variable("x".to_string())),
            )))
        );
    }

    #[test]
    fn lambda_with_type_annotation() {
        let p = parse("\\(x : int) => x;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::int()))),
                Box::new(Expr::Variable("x".to_string())),
            )))
        );
    }

    #[test]
    fn nested_lambda() {
        let p = parse("\\x => \\y => x;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                Box::new(Expr::Abstraction(
                    Box::new(Binding("y".to_string(), mono(Monotype::infer()))),
                    Box::new(Expr::Variable("x".to_string())),
                )),
            )))
        );
    }

    #[test]
    fn lambda_with_function_type_annotation() {
        let p = parse("\\(f : int => bool) => f;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Abstraction(
                Box::new(Binding("f".to_string(), mono(Monotype::func(vec![Monotype::int(), Monotype::bool()])))),
                Box::new(Expr::Variable("f".to_string())),
            )))
        );
    }

    // ---- Let-in expression ----

    #[test]
    fn let_in() {
        let p = parse("let x = 1 in x;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Let(
                "x".to_string(),
                Box::new(Expr::Literal(Box::new(Lit::Int(1)))),
                Box::new(Expr::Variable("x".to_string())),
            )))
        );
    }

    #[test]
    fn let_in_with_complex_body() {
        let p = parse("let x = 1 in let y = 2 in x;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Let(
                "x".to_string(),
                Box::new(Expr::Literal(Box::new(Lit::Int(1)))),
                Box::new(Expr::Let(
                    "y".to_string(),
                    Box::new(Expr::Literal(Box::new(Lit::Int(2)))),
                    Box::new(Expr::Variable("x".to_string())),
                )),
            )))
        );
    }

    // ---- If-else ----

    #[test]
    fn if_else() {
        let p = parse("if true then 1 else 2;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::IfElse(
                Box::new(Expr::Literal(Box::new(Lit::Bool(true)))),
                Box::new(Expr::Literal(Box::new(Lit::Int(1)))),
                Box::new(Expr::Literal(Box::new(Lit::Int(2)))),
            )))
        );
    }

    #[test]
    fn if_else_with_variable_condition() {
        let p = parse("if x then y else z;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::IfElse(
                Box::new(Expr::Variable("x".to_string())),
                Box::new(Expr::Variable("y".to_string())),
                Box::new(Expr::Variable("z".to_string())),
            )))
        );
    }

    #[test]
    fn nested_if_else() {
        let p = parse("if true then if false then 1 else 2 else 3;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::IfElse(
                Box::new(Expr::Literal(Box::new(Lit::Bool(true)))),
                Box::new(Expr::IfElse(
                    Box::new(Expr::Literal(Box::new(Lit::Bool(false)))),
                    Box::new(Expr::Literal(Box::new(Lit::Int(1)))),
                    Box::new(Expr::Literal(Box::new(Lit::Int(2)))),
                )),
                Box::new(Expr::Literal(Box::new(Lit::Int(3)))),
            )))
        );
    }

    // ---- Parenthesized expressions ----

    #[test]
    fn parenthesized_variable() {
        let p = parse("(x);");
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Variable("x".to_string()))));
    }

    #[test]
    fn parenthesized_application() {
        let p = parse("(f x);");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Application(
                Box::new(Expr::Variable("f".to_string())),
                Box::new(Expr::Variable("x".to_string())),
            )))
        );
    }

    // ---- Statements ----

    #[test]
    fn let_decl_without_type() {
        let p = parse("let x = 42;");
        assert_eq!(
            first(&p),
            &Stmt::Decl(
                Box::new(Expr::Variable("x".to_string())),
                mono(Monotype::infer()),
                Box::new(Expr::Literal(Box::new(Lit::Int(42)))),
            )
        );
    }

    #[test]
    fn let_decl_with_type() {
        let p = parse("let x : int = 42;");
        assert_eq!(
            first(&p),
            &Stmt::Decl(
                Box::new(Expr::Variable("x".to_string())),
                mono(Monotype::int()),
                Box::new(Expr::Literal(Box::new(Lit::Int(42)))),
            )
        );
    }

    #[test]
    fn let_decl_with_function_type() {
        let p = parse("let f : int => int = \\x => x;");
        assert_eq!(
            first(&p),
            &Stmt::Decl(
                Box::new(Expr::Variable("f".to_string())),
                mono(Monotype::func(vec![Monotype::int(), Monotype::int()])),
                Box::new(Expr::Abstraction(
                    Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                    Box::new(Expr::Variable("x".to_string())),
                )),
            )
        );
    }

    #[test]
    fn let_decl_with_bool_type() {
        let p = parse("let b : bool = true;");
        assert_eq!(
            first(&p),
            &Stmt::Decl(
                Box::new(Expr::Variable("b".to_string())),
                mono(Monotype::bool()),
                Box::new(Expr::Literal(Box::new(Lit::Bool(true)))),
            )
        );
    }

    #[test]
    fn print_statement() {
        let p = parse("print x;");
        assert_eq!(
            first(&p),
            &Stmt::Print(Box::new(Expr::Variable("x".to_string())))
        );
    }

    #[test]
    fn print_literal() {
        let p = parse("print 42;");
        assert_eq!(
            first(&p),
            &Stmt::Print(Box::new(Expr::Literal(Box::new(Lit::Int(42)))))
        );
    }

    // ---- Types ----

    #[test]
    fn simple_type_int() {
        let p = parse("let x : int = 0;");
        match first(&p) {
            Stmt::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::int()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_bool() {
        let p = parse("let x : bool = true;");
        match first(&p) {
            Stmt::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::bool()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_float() {
        let p = parse("let x : float = 1.0;");
        match first(&p) {
            Stmt::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::float()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_str() {
        let p = parse(r#"let x : str = "hi";"#);
        match first(&p) {
            Stmt::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::string()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_unit() {
        let p = parse("let x : () = ();");
        match first(&p) {
            Stmt::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::unit()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn function_type() {
        let p = parse("let f : int => bool = true;");
        match first(&p) {
            Stmt::Decl(_, typ, _) => {
                assert_eq!(typ.t, Monotype::func(vec![Monotype::int(), Monotype::bool()]))
            }
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn nested_function_type() {
        let p = parse("let f : int => bool => str = true;");
        match first(&p) {
            Stmt::Decl(_, typ, _) => {
                assert_eq!(
                    typ.t,
                    Monotype::func(vec![
                        Monotype::int(),
                        Monotype::func(vec![Monotype::bool(), Monotype::string()])
                    ])
                )
            }
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    // ---- Programs ----

    #[test]
    fn empty_program() {
        let p = parse("");
        assert!(p.stmts.is_empty());
    }

    #[test]
    fn single_statement_no_semicolon() {
        let p = parse("42");
        assert_eq!(p.stmts.len(), 1);
        assert_eq!(first(&p), &Stmt::Expr(Box::new(Expr::Literal(Box::new(Lit::Int(42))))));
    }

    #[test]
    fn multiple_statements() {
        let p = parse("let x = 1; let y = 2;");
        assert_eq!(p.stmts.len(), 2);
        match &p.stmts[0] {
            Stmt::Decl(name, _, _) => assert_eq!(**name, Expr::Variable("x".to_string())),
            other => panic!("expected Decl, got {:?}", other),
        }
        match &p.stmts[1] {
            Stmt::Decl(name, _, _) => assert_eq!(**name, Expr::Variable("y".to_string())),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn mixed_statement_types() {
        let p = parse("let x = 1; print x; x;");
        assert_eq!(p.stmts.len(), 3);
        assert!(matches!(first(&p), Stmt::Decl(..)));
        assert!(matches!(&p.stmts[1], Stmt::Print(..)));
        assert!(matches!(&p.stmts[2], Stmt::Expr(..)));
    }

    #[test]
    fn last_statement_needs_no_semicolon() {
        let p = parse("let x = 1; let y = 2");
        assert_eq!(p.stmts.len(), 2);
    }

    // ---- Complex / integration ----

    #[test]
    fn complex_nested_expression() {
        let p = parse("if true then let x = \\(a : int) => a in x 1 else 0;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::IfElse(
                Box::new(Expr::Literal(Box::new(Lit::Bool(true)))),
                Box::new(Expr::Let(
                    "x".to_string(),
                    Box::new(Expr::Abstraction(
                        Box::new(Binding("a".to_string(), mono(Monotype::int()))),
                        Box::new(Expr::Variable("a".to_string())),
                    )),
                    Box::new(Expr::Application(
                        Box::new(Expr::Variable("x".to_string())),
                        Box::new(Expr::Literal(Box::new(Lit::Int(1)))),
                    )),
                )),
                Box::new(Expr::Literal(Box::new(Lit::Int(0)))),
            )))
        );
    }

    #[test]
    fn identity_function_applied() {
        let p = parse("\\x => x y;");
        assert_eq!(
            first(&p),
            &Stmt::Expr(Box::new(Expr::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                Box::new(Expr::Application(
                    Box::new(Expr::Variable("x".to_string())),
                    Box::new(Expr::Variable("y".to_string())),
                )),
            )))
        );
    }

    #[test]
    fn multi_arg_function_type() {
        let p = parse("let f : int => bool => str = 0;");
        match first(&p) {
            Stmt::Decl(_, typ, _) => {
                assert_eq!(
                    typ.t,
                    Monotype::func(vec![
                        Monotype::int(),
                        Monotype::func(vec![Monotype::bool(), Monotype::string()])
                    ])
                )
            }
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    // ---- Error cases ----

    #[test]
    fn empty_input_is_valid() {
        let p = parse("");
        assert!(p.stmts.is_empty());
    }

    #[test]
    fn syntax_error_returns_err() {
        let result = Program::parse("===");
        assert!(result.is_err());
    }

    #[test]
    fn incomplete_let_returns_err() {
        let result = Program::parse("let");
        assert!(result.is_err());
    }

    #[test]
    fn unmatched_paren_returns_err() {
        let result = Program::parse("(x;");
        assert!(result.is_err());
    }
}

