use crate::types::*;
use crate::grammar;

#[derive(Debug, Clone, PartialEq)]
pub struct Pos {
    start : (u32, u32),
    end : (u32, u32)
}

impl Pos {
    pub fn nil() -> Pos {
        Pos { start : (0, 0), end : (0, 0) }
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDec {
    Alias(Box<Type>),
    Enum(Vec<Variant>)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub n : String,
    pub tparams : Vec<Type>
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeHeader {
    pub n : String,
    pub tvars : Vec<String>
}

#[derive(Debug, PartialEq)]
pub enum SNode {
    Decl(Box<Expr>, Box<Type>, Box<Expr>),  // let x [: Type] = e;
    Expr(Box<Expr>),                        // e; special case, not always ()
    Print(Box<Expr>),                       // print e;
    TypeDecl(TypeHeader, Box<TypeDec>) // name <type vars> = <type>
}

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub s : Box<SNode>,
    pub ctx : TypeContext,
    pub pos : Pos
    // TODO
}

impl Stmt {
    pub fn from(node : SNode) -> Stmt {
        Stmt {
            s : Box::new(node),
            ctx : TypeContext::new(),
            pos : Pos::nil()
        }
    }

    pub fn typecheck(&mut self, ctx : &TypeContext) -> Result<(Substitution, Monotype), UnificationError> {
        let mut context = ctx.clone();
        match &*self.s {
            SNode::Decl(e1, t1, e2) => {
                let var_name = match &*e1.e {
                    ENode::Variable(name) => name.clone(),
                    _ => return Err(UnificationError { message: format!("Expected a variable name in declaration, got {:?}", *e1.e) }),
                };
                let binding_type = type_to_typefn(t1, &mut context)?;
                let old_binding = context.get(&var_name);
                context.add(var_name.clone(), Polytype::Mono(Box::new(binding_type.clone())));
                let (s1, inferred_type) = algo_w(&mut context, e2)?;
                let s2 = unify(&binding_type.apply(&s1), &inferred_type)?;
                let combined = s1.combine(s2);
                context = context.apply(&combined);
                match old_binding {
                    Some(poly) => context.add(var_name.clone(), poly),
                    None => context.remove(&var_name),
                }
                let resolved_typ = binding_type.apply(&combined);
                let generalized = context.generalise(&resolved_typ);
                context.add(var_name, generalized);
                self.ctx = context;
                Ok((combined, resolved_typ))
            },
            SNode::Expr(e1) => {
                let (sub, typ) = algo_w(&mut context, e1)?;
                self.ctx = context.apply(&sub);
                Ok((sub, typ))
            },
            SNode::Print(e1) => {
                let (s1, t1) = algo_w(&mut context, e1)?;
                let s2 = unify(&t1, &Monotype::string())?;
                let combined = s1.combine(s2);
                context = context.apply(&combined);
                self.ctx = context;
                Ok((combined, Monotype::unit()))
            },
            SNode::TypeDecl(header, dec) => {
                handle_type_decl(header, dec, &mut context)?;
                self.ctx = context;
                Ok((Substitution::new(), Monotype::unit()))
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ENode {
    Variable(String),
    Literal(Box<Lit>),
    Abstraction(Box<Binding>, Box<Expr>),
    Application(Box<Expr>, Box<Expr>),
    Let(String,Box<Expr>,Box<Expr>),
    IfElse(Box<Expr>,Box<Expr>,Box<Expr>),
    Block(Vec<Stmt>, Box<Expr>),
    Comparison(CompOp, Box<Expr>, Box<Expr>),
    Arithmetic(ArithOp, Box<Expr>, Box<Expr>),
    Logical(LogicalOp, Box<Expr>, Box<Expr>),
    Unary(UnaryOp, Box<Expr>),
    List(Vec<Expr>),
    Cons(Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<MatchCase>)
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub e : Box<ENode>,
    pub ctx : TypeContext,
    pub pos : Pos
}

impl Expr {
    pub fn from(node : ENode) -> Expr {
        Expr {
            e : Box::new(node),
            ctx : TypeContext::new(),
            pos : Pos::nil()
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct MatchCase {
    pub val : Box<Expr>,
    pub exp : Box<Expr>
}

#[derive(Debug, Clone, PartialEq)]
pub enum CompOp {
    Eq,
    NotEq,
    Less,
    Greater,
    LessEq,
    GreatEq,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ArithOp {
    Plus,
    Minus,
    Div,
    Times,
    Mod,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LogicalOp {
    And,
    Or,
    Xor,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Negate,
    Not
}

#[derive(Debug)]
pub struct Program {
    pub stmts : Vec<Stmt>,
    pub ctx : TypeContext
}

impl Program {
    pub fn parse(buf : &str) -> Result<Box<Program>, String> {
        grammar::ProgParser::new().parse(buf).map_err(|e| format!("{}", e))
    }

    pub fn typecheck(prog : &mut Program) -> Result<(), UnificationError> {
        for stmt in prog.stmts.iter_mut() {
            stmt.typecheck(&prog.ctx)?;
            prog.ctx = stmt.ctx.clone();
        }
        Ok(())
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
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42)))))));
    }

    #[test]
    fn negative_int_literal() {
        let p = parse("-7;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Unary(
            UnaryOp::Negate,
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(7))))),
        )))));
    }

    #[test]
    fn float_literal() {
        let p = parse("3.14;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Float(3.14)))))));
    }

    #[test]
    fn negative_float_literal() {
        let p = parse("-2.5;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Unary(
            UnaryOp::Negate,
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Float(2.5))))),
        )))));
    }

    #[test]
    fn bool_true_literal() {
        let p = parse("true;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true)))))));
    }

    #[test]
    fn bool_false_literal() {
        let p = parse("false;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(false)))))));
    }

    #[test]
    fn string_literal() {
        let p = parse(r#""hello";"#);
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Str("hello".to_string())))))));
    }

    #[test]
    fn empty_string_literal() {
        let p = parse(r#""";"#);
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Str("".to_string())))))));
    }

    #[test]
    fn unit_literal() {
        let p = parse("();");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Unit))))));
    }

    // ---- Variables ----

    #[test]
    fn simple_variable() {
        let p = parse("x;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Variable("x".to_string())))));
    }

    #[test]
    fn underscore_variable() {
        let p = parse("_foo;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Variable("_foo".to_string())))));
    }

    #[test]
    fn alphanumeric_variable() {
        let p = parse("x2y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Variable("x2y".to_string())))));
    }

    // ---- Application ----

    #[test]
    fn single_application() {
        let p = parse("f x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Application(
                Box::new(Expr::from(ENode::Variable("f".to_string()))),
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn left_associative_application() {
        let p = parse("f x y;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Application(
                Box::new(Expr::from(ENode::Application(
                    Box::new(Expr::from(ENode::Variable("f".to_string()))),
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
                Box::new(Expr::from(ENode::Variable("y".to_string()))),
            ))))
        );
    }

    #[test]
    fn application_with_literal_arg() {
        let p = parse("f 42;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Application(
                Box::new(Expr::from(ENode::Variable("f".to_string()))),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))),
            ))))
        );
    }

    #[test]
    fn application_with_parenthesized_expr() {
        let p = parse("f (g x);");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Application(
                Box::new(Expr::from(ENode::Variable("f".to_string()))),
                Box::new(Expr::from(ENode::Application(
                    Box::new(Expr::from(ENode::Variable("g".to_string()))),
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
            ))))
        );
    }

    // ---- Block expressions ----

    #[test]
    fn block_only_expression() {
        let p = parse("{ 42 };");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Block(
                vec![],
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))),
            ))))
        );
    }

    #[test]
    fn block_with_one_let() {
        let p = parse("{ let x = 1; x };");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Block(
                vec![Stmt::from(SNode::Decl(
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                    Box::new(Type { t: Monotype::infer() }),
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                ))],
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn block_with_multiple_stmts() {
        let p = parse("{ let x = 1; let y = 2; x };");
        let block = match &*first(&p).s {
            SNode::Expr(e) => &*e.e,
            _ => panic!("expected Expr"),
        };
        let ENode::Block(stmts, expr) = block else {
            panic!("expected Block");
        };
        assert_eq!(stmts.len(), 2);
        assert!(matches!(&*stmts[0].s, SNode::Decl(..)));
        assert!(matches!(&*stmts[1].s, SNode::Decl(..)));
        assert_eq!(&*expr.e, &ENode::Variable("x".to_string()));
    }

    #[test]
    fn block_in_let_rhs() {
        let p = parse("let x = { 42 };");
        assert_eq!(
            &*first(&p).s,
            &SNode::Decl(
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
                Box::new(Type { t: Monotype::infer() }),
                Box::new(Expr::from(ENode::Block(
                    vec![],
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))),
                ))),
            )
        );
    }

    #[test]
    fn block_in_if_else_branches() {
        let p = parse("if true then { 1 } else { 2 };");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::IfElse(
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
                Box::new(Expr::from(ENode::Block(
                    vec![],
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                ))),
                Box::new(Expr::from(ENode::Block(
                    vec![],
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(2))))),
                ))),
            ))))
        );
    }

    #[test]
    fn nested_block() {
        let p = parse("{ { 42 } };");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Block(
                vec![],
                Box::new(Expr::from(ENode::Block(
                    vec![],
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))),
                ))),
            ))))
        );
    }

    #[test]
    fn block_with_print() {
        let p = parse(r#"{ print "hi"; 42 };"#);
        let block = match &*first(&p).s {
            SNode::Expr(e) => &*e.e,
            _ => panic!("expected Expr"),
        };
        let ENode::Block(stmts, expr) = block else {
            panic!("expected Block");
        };
        assert_eq!(stmts.len(), 1);
        assert!(matches!(&*stmts[0].s, SNode::Print(..)));
        assert_eq!(&*expr.e, &ENode::Literal(Box::new(Lit::Int(42))));
    }

    // ---- Abstraction ----

    #[test]
    fn lambda_without_type_annotation() {
        let p = parse("\\x => x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn lambda_with_type_annotation() {
        let p = parse("\\(x : int) => x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::int()))),
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn nested_lambda() {
        let p = parse("\\x => \\y => x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                Box::new(Expr::from(ENode::Abstraction(
                    Box::new(Binding("y".to_string(), mono(Monotype::infer()))),
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
            ))))
        );
    }

    #[test]
    fn lambda_with_function_type_annotation() {
        let p = parse("\\(f : int => bool) => f;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Abstraction(
                Box::new(Binding("f".to_string(), mono(Monotype::func(vec![Monotype::int(), Monotype::bool()])))),
                Box::new(Expr::from(ENode::Variable("f".to_string()))),
            ))))
        );
    }

    // ---- Let-in expression ----

    #[test]
    fn let_in() {
        let p = parse("let x = 1 in x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Let(
                "x".to_string(),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn let_in_with_complex_body() {
        let p = parse("let x = 1 in let y = 2 in x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Let(
                "x".to_string(),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                Box::new(Expr::from(ENode::Let(
                    "y".to_string(),
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(2))))),
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
            ))))
        );
    }

    // ---- If-else ----

    #[test]
    fn if_else() {
        let p = parse("if true then 1 else 2;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::IfElse(
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(2))))),
            ))))
        );
    }

    #[test]
    fn if_else_with_variable_condition() {
        let p = parse("if x then y else z;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::IfElse(
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
                Box::new(Expr::from(ENode::Variable("y".to_string()))),
                Box::new(Expr::from(ENode::Variable("z".to_string()))),
            ))))
        );
    }

    #[test]
    fn nested_if_else() {
        let p = parse("if true then if false then 1 else 2 else 3;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::IfElse(
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
                Box::new(Expr::from(ENode::IfElse(
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(false))))),
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                    Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(2))))),
                ))),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(3))))),
            ))))
        );
    }

    // ---- Parenthesized expressions ----

    #[test]
    fn parenthesized_variable() {
        let p = parse("(x);");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Variable("x".to_string())))));
    }

    #[test]
    fn parenthesized_application() {
        let p = parse("(f x);");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Application(
                Box::new(Expr::from(ENode::Variable("f".to_string()))),
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    // ---- Statements ----

    #[test]
    fn let_decl_without_type() {
        let p = parse("let x = 42;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Decl(
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
                mono(Monotype::infer()),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))),
            )
        );
    }

    #[test]
    fn let_decl_with_type() {
        let p = parse("let x : int = 42;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Decl(
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
                mono(Monotype::int()),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))),
            )
        );
    }

    #[test]
    fn let_decl_with_function_type() {
        let p = parse("let f : int => int = \\x => x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Decl(
                Box::new(Expr::from(ENode::Variable("f".to_string()))),
                mono(Monotype::func(vec![Monotype::int(), Monotype::int()])),
                Box::new(Expr::from(ENode::Abstraction(
                    Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
            )
        );
    }

    #[test]
    fn let_decl_with_bool_type() {
        let p = parse("let b : bool = true;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Decl(
                Box::new(Expr::from(ENode::Variable("b".to_string()))),
                mono(Monotype::bool()),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
            )
        );
    }

    #[test]
    fn print_statement() {
        let p = parse("print x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Print(Box::new(Expr::from(ENode::Variable("x".to_string()))))
        );
    }

    #[test]
    fn print_literal() {
        let p = parse("print 42;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Print(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42))))))
        );
    }

    // ---- Types ----

    #[test]
    fn simple_type_int() {
        let p = parse("let x : int = 0;");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::int()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_bool() {
        let p = parse("let x : bool = true;");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::bool()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_float() {
        let p = parse("let x : float = 1.0;");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::float()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_str() {
        let p = parse(r#"let x : str = "hi";"#);
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::string()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn simple_type_unit() {
        let p = parse("let x : () = ();");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => assert_eq!(typ.t, Monotype::unit()),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn function_type() {
        let p = parse("let f : int => bool = true;");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => {
                assert_eq!(typ.t, Monotype::func(vec![Monotype::int(), Monotype::bool()]))
            }
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn nested_function_type() {
        let p = parse("let f : int => bool => str = true;");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => {
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
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(42)))))));
    }

    #[test]
    fn multiple_statements() {
        let p = parse("let x = 1; let y = 2;");
        assert_eq!(p.stmts.len(), 2);
        match &*p.stmts[0].s {
            SNode::Decl(name, _, _) => assert_eq!(**name, Expr::from(ENode::Variable("x".to_string()))),
            other => panic!("expected Decl, got {:?}", other),
        }
        match &*p.stmts[1].s {
            SNode::Decl(name, _, _) => assert_eq!(**name, Expr::from(ENode::Variable("y".to_string()))),
            other => panic!("expected Decl, got {:?}", other),
        }
    }

    #[test]
    fn mixed_statement_types() {
        let p = parse("let x = 1; print x; x;");
        assert_eq!(p.stmts.len(), 3);
        assert!(matches!(&*first(&p).s, SNode::Decl(..)));
        assert!(matches!(&*p.stmts[1].s, SNode::Print(..)));
        assert!(matches!(&*p.stmts[2].s, SNode::Expr(..)));
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
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::IfElse(
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
                Box::new(Expr::from(ENode::Let(
                    "x".to_string(),
                    Box::new(Expr::from(ENode::Abstraction(
                        Box::new(Binding("a".to_string(), mono(Monotype::int()))),
                        Box::new(Expr::from(ENode::Variable("a".to_string()))),
                    ))),
                    Box::new(Expr::from(ENode::Application(
                        Box::new(Expr::from(ENode::Variable("x".to_string()))),
                        Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
                    ))),
                ))),
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(0))))),
            ))))
        );
    }

    #[test]
    fn identity_function_applied() {
        let p = parse("\\x => x y;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Abstraction(
                Box::new(Binding("x".to_string(), mono(Monotype::infer()))),
                Box::new(Expr::from(ENode::Application(
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                    Box::new(Expr::from(ENode::Variable("y".to_string()))),
                ))),
            ))))
        );
    }

    #[test]
    fn multi_arg_function_type() {
        let p = parse("let f : int => bool => str = 0;");
        match &*first(&p).s {
            SNode::Decl(_, typ, _) => {
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

    // ---- Unary expressions ---- 

    #[test]
    fn negate_variable() {
        let p = parse("-x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Unary(
                UnaryOp::Negate,
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn not_variable() {
        let p = parse("!x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Unary(
                UnaryOp::Not,
                Box::new(Expr::from(ENode::Variable("x".to_string()))),
            ))))
        );
    }

    #[test]
    fn not_true() {
        let p = parse("!true;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Unary(
                UnaryOp::Not,
                Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
            ))))
        );
    }

    #[test]
    fn double_negation() {
        let p = parse("--x;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Unary(
                UnaryOp::Negate,
                Box::new(Expr::from(ENode::Unary(
                    UnaryOp::Negate,
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
            ))))
        );
    }

    #[test]
    fn negate_precedence_over_mul() {
        let p = parse("-x * y;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Arithmetic(
                ArithOp::Times,
                Box::new(Expr::from(ENode::Unary(
                    UnaryOp::Negate,
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
                Box::new(Expr::from(ENode::Variable("y".to_string()))),
            ))))
        );
    }

    #[test]
    fn not_precedence_over_and() {
        let p = parse("!x && y;");
        assert_eq!(
            &*first(&p).s,
            &SNode::Expr(Box::new(Expr::from(ENode::Logical(
                LogicalOp::And,
                Box::new(Expr::from(ENode::Unary(
                    UnaryOp::Not,
                    Box::new(Expr::from(ENode::Variable("x".to_string()))),
                ))),
                Box::new(Expr::from(ENode::Variable("y".to_string()))),
            ))))
        );
    }

    // ---- Whole program typechecking ----

    #[test]
    fn typecheck_empty_program() {
        let mut p = parse("");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_int_literal() {
        let mut p = parse("42;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_let_decl() {
        let mut p = parse("let x = 42;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_let_and_use() {
        let mut p = parse("let x = 42; x;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_let_annotated() {
        let mut p = parse("let x : int = 42; x;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_let_wrong_annotation() {
        let mut p = parse("let x : bool = 42;");
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_function_application() {
        let mut p = parse("let f = \\x => x; f 42;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_print_string() {
        let mut p = parse(r#"print "hi";"#);
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_print_non_string() {
        let mut p = parse("print 42;");
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_undefined_variable() {
        let mut p = parse("x;");
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_multiple_decls() {
        let mut p = parse("let x = 1; let y = 2; x; y;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_polymorphic_let() {
        let mut p = parse("let id = \\x => x; id 42; id true;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_recursive_let_simple() {
        let src = r"let loop = \(x : int) => if x > 0 then loop 0 else 0;";
        let mut p = parse(src);
        match Program::typecheck(&mut p) {
            Ok(_) => {},
            Err(e) => panic!("type error: {}", e),
        }
    }

    #[test]
    fn typecheck_recursive_let() {
        let src = r"let rec = \(x : int) => if x > 0 then rec (x * 1) else 0;";
        let mut p = parse(src);
        match Program::typecheck(&mut p) {
            Ok(_) => {},
            Err(e) => panic!("type error: {}", e),
        }
    }

    #[test]
    fn typecheck_if_else() {
        let mut p = parse("if true then 1 else 2;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_if_else_non_bool_cond() {
        let mut p = parse("if 1 then 2 else 3;");
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_if_else_branch_mismatch() {
        let mut p = parse("if true then 1 else true;");
        assert!(Program::typecheck(&mut p).is_err());
    }

    // ---- Binary expressions ----

    #[test]
    fn arith_plus() {
        let p = parse("1 + 2;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Arithmetic(
            ArithOp::Plus,
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(2))))),
        )))));
    }

    #[test]
    fn arith_minus() {
        let p = parse("x - y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Arithmetic(
            ArithOp::Minus,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn arith_times() {
        let p = parse("a * b;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Arithmetic(
            ArithOp::Times,
            Box::new(Expr::from(ENode::Variable("a".to_string()))),
            Box::new(Expr::from(ENode::Variable("b".to_string()))),
        )))));
    }

    #[test]
    fn arith_div() {
        let p = parse("a / b;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Arithmetic(
            ArithOp::Div,
            Box::new(Expr::from(ENode::Variable("a".to_string()))),
            Box::new(Expr::from(ENode::Variable("b".to_string()))),
        )))));
    }

    #[test]
    fn arith_mod() {
        let p = parse("x % y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Arithmetic(
            ArithOp::Mod,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn comp_eq() {
        let p = parse("x == y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Comparison(
            CompOp::Eq,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn comp_not_eq() {
        let p = parse("x != y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Comparison(
            CompOp::NotEq,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn comp_less() {
        let p = parse("1 < 2;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Comparison(
            CompOp::Less,
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(1))))),
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Int(2))))),
        )))));
    }

    #[test]
    fn comp_greater() {
        let p = parse("x > y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Comparison(
            CompOp::Greater,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn comp_less_eq() {
        let p = parse("x <= y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Comparison(
            CompOp::LessEq,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn comp_great_eq() {
        let p = parse("x >= y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Comparison(
            CompOp::GreatEq,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn logic_and() {
        let p = parse("true && false;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Logical(
            LogicalOp::And,
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(true))))),
            Box::new(Expr::from(ENode::Literal(Box::new(Lit::Bool(false))))),
        )))));
    }

    #[test]
    fn logic_or() {
        let p = parse("x || y;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Logical(
            LogicalOp::Or,
            Box::new(Expr::from(ENode::Variable("x".to_string()))),
            Box::new(Expr::from(ENode::Variable("y".to_string()))),
        )))));
    }

    #[test]
    fn logic_xor() {
        let p = parse("a ^ b;");
        assert_eq!(&*first(&p).s, &SNode::Expr(Box::new(Expr::from(ENode::Logical(
            LogicalOp::Xor,
            Box::new(Expr::from(ENode::Variable("a".to_string()))),
            Box::new(Expr::from(ENode::Variable("b".to_string()))),
        )))));
    }

    // ---- Unary typechecking ----

    #[test]
    fn typecheck_negate_int() {
        let mut p = parse("-5;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_negate_float() {
        let mut p = parse("-3.14;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_negate_string_error() {
        let mut p = parse(r#"-"hi";"#);
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_not_bool() {
        let mut p = parse("!true;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_not_int_error() {
        let mut p = parse("!5;");
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_not_string_error() {
        let mut p = parse(r#"!"hi";"#);
        assert!(Program::typecheck(&mut p).is_err());
    }

    #[test]
    fn typecheck_negate_in_let() {
        let mut p = parse("let x : int = -5; x;");
        assert!(Program::typecheck(&mut p).is_ok());
    }

    #[test]
    fn typecheck_not_in_if_cond() {
        let mut p = parse("if !false then 1 else 2;");
        assert!(Program::typecheck(&mut p).is_ok());
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

