use crate::{ast::Expr::Variable, types::*};

#[derive(Debug)]
pub enum Lit {
    Int(i32),
    Float(f32),
    Bool(bool),
    Str(String),
    Unit,
}

#[derive(Debug, Clone)]
pub enum Type {
    Infer,
    Unit,
    Int,
    Float,
    Bool,
    Str,
    Fn(Box<Type>,Box<Type>),
}

#[derive(Debug)]
pub struct Binding(pub String, pub Box<Type>);

#[derive(Debug)]
pub enum Stmt {
    Decl(Box<Expr>, Box<Type>, Box<Expr>),  // let x [: Type] = e;
    Expr(Box<Expr>),                        // e; special case, not always ()
    Print(Box<Expr>),                       // print e;
}

#[derive(Debug)]
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
    // TODO: Result return type
    pub fn typecheck() {
        let ctx = TypeContext::new();
        algo_w(&ctx, &Box::new(Variable(String::new())));
    }
}

