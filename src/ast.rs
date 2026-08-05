use crate::prelude::get_prelude;
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

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub enum SNode {
    Decl(Box<Expr>, Box<Type>, Box<Expr>),  // let x [: Type] = e;
    Expr(Box<Expr>),                        // e; special case, not always ()
    TypeDecl(TypeHeader, Box<TypeDec>) // name <type vars> = <type>
}

#[derive(Debug, Clone, PartialEq)]
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
        let (combined, typ) = match &mut *self.s {
            SNode::Decl(e1, t1, e2) => {
                let var_name = match &*e1.e {
                    ENode::Variable(name) => name.clone(),
                    _ => return Err(UnificationError { message: format!("Expected a variable name in declaration, got {:?}", *e1.e) }),
                };
                if TypeContext::is_builtin(&var_name) {
                    return Err(UnificationError { message: format!("Redefinition of builtin function '{}' not allowed", var_name) });
                }
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
                (combined, resolved_typ)
            },
            SNode::Expr(e1) => {
                let (sub, typ) = algo_w(&mut context, e1)?;
                self.ctx = context.apply(&sub);
                (sub, typ)
            },
            SNode::TypeDecl(header, dec) => {
                handle_type_decl(header, dec, &mut context)?;
                self.ctx = context;
                (Substitution::new(), Monotype::unit())
            }
        };
        resolve_stmt_types(self, &combined);
        Ok((combined, typ))
    }
}

#[derive(Debug, Clone, PartialEq)]
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

/// Apply `sub` to the recorded (`algo_w`-annotated) type of every expression
/// reachable from `stmt`. Runs after a statement is type-checked, once the
/// statement's full substitution is known, resolving inferred types into
/// concrete ones. Type variables bound by a generalized `let` are resolved
/// too: codegen targets monomorphic MLIR, so each instantiation is specialized
/// at its use site rather than kept polymorphic.
pub fn resolve_stmt_types(stmt : &mut Stmt, sub : &Substitution) {
    match &mut *stmt.s {
        SNode::Decl(e1, _, e2) => {
            resolve_expr_types(e1, sub);
            resolve_expr_types(e2, sub);
        },
        SNode::Expr(e1) => resolve_expr_types(e1, sub),
        SNode::TypeDecl(_, _) => {}
    }
}

/// Apply `sub` to the recorded type of `expr` and everything reachable from
/// it. Used by codegen to specialize a lambda body: the definition statement
/// may leave free type variables (e.g. a recursive use), which the
/// instantiation's substitution replaces with concrete types.
pub fn apply_substitution(expr : &mut Expr, sub : &Substitution) {
    resolve_expr_types(expr, sub);
}

fn resolve_expr_types(expr : &mut Expr, sub : &Substitution) {
    expr.typ = expr.typ.apply(sub);
    match &mut *expr.e {
        ENode::Variable(_) | ENode::Literal(_) => {}
        ENode::Abstraction(_, body) => resolve_expr_types(body, sub),
        ENode::Application(f, x) => {
            resolve_expr_types(f, sub);
            resolve_expr_types(x, sub);
        },
        ENode::Let(_, e1, e2) => {
            resolve_expr_types(e1, sub);
            resolve_expr_types(e2, sub);
        },
        ENode::IfElse(c, t, e) => {
            resolve_expr_types(c, sub);
            resolve_expr_types(t, sub);
            resolve_expr_types(e, sub);
        },
        ENode::Block(stmts, e) => {
            for s in stmts.iter_mut() {
                resolve_stmt_types(s, sub);
            }
            resolve_expr_types(e, sub);
        },
        ENode::Comparison(_, a, b) => {
            resolve_expr_types(a, sub);
            resolve_expr_types(b, sub);
        },
        ENode::Arithmetic(_, a, b) => {
            resolve_expr_types(a, sub);
            resolve_expr_types(b, sub);
        },
        ENode::Logical(_, a, b) => {
            resolve_expr_types(a, sub);
            resolve_expr_types(b, sub);
        },
        ENode::Unary(_, e) => resolve_expr_types(e, sub),
        ENode::List(es) => {
            for e in es.iter_mut() {
                resolve_expr_types(e, sub);
            }
        },
        ENode::Cons(h, t) => {
            resolve_expr_types(h, sub);
            resolve_expr_types(t, sub);
        },
        ENode::Match(scrut, cases) => {
            resolve_expr_types(scrut, sub);
            for c in cases.iter_mut() {
                resolve_expr_types(&mut c.val, sub);
                resolve_expr_types(&mut c.exp, sub);
            }
        },
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub e : Box<ENode>,
    pub ctx : TypeContext,
    pub pos : Pos,
    /// The inferred type of this expression: filled with the raw type during
    /// typechecking (`algo_w`) and resolved by the post-typecheck pass
    /// ([`resolve_stmt_types`]) once the statement's full substitution is
    /// known.
    pub typ : Monotype,
}

impl Expr {
    pub fn from(node : ENode) -> Expr {
        Expr {
            e : Box::new(node),
            ctx : TypeContext::new(),
            pos : Pos::nil(),
            typ : Monotype::infer(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
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

    pub fn parse_with_prelude(buf : &str) -> Result<Box<Program>, String> {
        let mut program = Self::parse(buf)?;
        let prelude = get_prelude();
        program.stmts.splice(0..0, prelude.iter().cloned());
        Ok(program)
    }

    pub fn typecheck(prog : &mut Program) -> Result<(), UnificationError> {
        for stmt in prog.stmts.iter_mut() {
            stmt.typecheck(&prog.ctx)?;
            prog.ctx = stmt.ctx.clone();
        }
        Ok(())
    }
}
