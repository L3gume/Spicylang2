use crate::prelude::get_prelude;
use crate::types::*;
use crate::grammar;

#[derive(Debug, Clone, PartialEq)]
pub struct Pos {
    /// 1-based source span. Filled by `Program::parse` from the byte offsets
    /// that the grammar records; all-zero for synthetic/nil positions.
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
    /// Raw byte offsets into the parsed buffer (the values the grammar's
    /// `@L`/`@R` produce). Kept so positions can be re-indexed; unused by
    /// codegen once the line/column span is filled.
    pub start: u32,
    pub end: u32,
}

impl Pos {
    pub fn nil() -> Pos {
        Pos { start_line: 0, start_col: 0, end_line: 0, end_col: 0, start: 0, end: 0 }
    }

    /// A raw byte-offset span, as produced by the parser's `@L`/`@R`. The
    /// line/column fields are filled in by [`Program::parse`].
    pub fn bytes(start: u32, end: u32) -> Pos {
        Pos { start_line: 0, start_col: 0, end_line: 0, end_col: 0, start, end }
    }

    pub fn is_nil(&self) -> bool {
        self.start == 0 && self.end == 0
    }

    /// Convert the raw byte offsets into a 1-based (line, column) span using
    /// the buffer's line index.
    pub fn fill(&mut self, index: &LineIndex) {
        let (sl, sc) = index.line_col(self.start);
        let (el, ec) = index.line_col(self.end);
        self.start_line = sl;
        self.start_col = sc;
        self.end_line = el;
        self.end_col = ec;
    }

    /// The span covering both `self` and `other` (min start, max end),
    /// re-filling the line/column fields for the combined byte range.
    pub fn merge(&mut self, other: &Pos) {
        self.start = self.start.min(other.start);
        self.end = self.end.max(other.end);
        self.start_line = 0;
        self.start_col = 0;
        self.end_line = 0;
        self.end_col = 0;
    }
}

/// A line index over a parsed buffer, used to convert byte offsets to
/// 1-based (line, column) positions.
#[derive(Debug, Clone)]
pub struct LineIndex {
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(buf: &str) -> LineIndex {
        let mut line_starts = vec![0];
        for (i, b) in buf.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
            }
        }
        LineIndex { line_starts }
    }

    /// 1-based (line, column) for a byte offset.
    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        (line as u32 + 1, offset - self.line_starts[line] + 1)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i32),
    Float(f32),
    Bool(bool),
    Str(String),
    Char(char),
    Unit,
}

/// Decode the escape sequence beginning at `\` (with the iterator already past
/// the backslash), returning the character it denotes. Supported escapes are
/// `\n`, `\t`, `\r`, `\0`, `\a`, `\b`, `\f`, `\v`, `\\`, `\'`, `\"`, `\xHH`,
/// and `\u{...}`. An unknown escape yields the escaped character itself (so
/// `\q` is `q`).
fn decode_escape(chars: &mut std::str::Chars) -> char {
    match chars.next() {
        Some('n') => '\n',
        Some('t') => '\t',
        Some('r') => '\r',
        Some('0') => '\0',
        Some('a') => '\x07',
        Some('b') => '\x08',
        Some('f') => '\x0c',
        Some('v') => '\x0b',
        Some('\\') => '\\',
        Some('\'') => '\'',
        Some('"') => '"',
        Some('x') => {
            let hex: String = chars.take(2).collect();
            let code = u32::from_str_radix(&hex, 16).unwrap_or(0);
            char::from_u32(code).unwrap_or('\0')
        }
        Some('u') => {
            chars.next(); // '{'
            let digits: String = chars.take_while(|c| *c != '}').collect();
            let code = u32::from_str_radix(&digits, 16).unwrap_or(0);
            char::from_u32(code).unwrap_or('\0')
        }
        Some(other) => other,
        None => '\0',
    }
}

/// Decode a single-quoted char literal (including its quotes), resolving the
/// escape sequences handled by [`decode_escape`].
pub(crate) fn decode_char_literal(raw: &str) -> char {
    let inner = &raw[1..raw.len().saturating_sub(1)];
    let mut chars = inner.chars();
    match chars.next() {
        None => '\0',
        Some('\\') => decode_escape(&mut chars),
        Some(c) => c,
    }
}

/// Decode a double-quoted string literal (including its quotes), resolving
/// escape sequences with the same rules as [`decode_char_literal`].
pub(crate) fn decode_string_literal(raw: &str) -> String {
    let inner = &raw[1..raw.len().saturating_sub(1)];
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            out.push(decode_escape(&mut chars));
        } else {
            out.push(c);
        }
    }
    out
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

#[derive(Debug, Clone)]
pub struct Stmt {
    pub s : Box<SNode>,
    pub ctx : TypeContext,
    pub pos : Pos
    // TODO
}

impl PartialEq for Stmt {
    /// Structural equality: source positions are metadata and deliberately
    /// excluded so parsed trees compare equal to hand-built expected trees.
    fn eq(&self, other: &Self) -> bool {
        self.s == other.s && self.ctx == other.ctx
    }
}

impl Stmt {
    pub fn from(node : SNode) -> Stmt {
        Self::at(Pos::nil(), node)
    }

    pub fn at(pos : Pos, node : SNode) -> Stmt {
        Stmt {
            s : Box::new(node),
            ctx : TypeContext::new(),
            pos
        }
    }

    pub fn typecheck(&mut self, ctx : &TypeContext) -> Result<(Substitution, Monotype), UnificationError> {
        let result = (|| -> Result<(Substitution, Monotype), UnificationError> {
            let mut context = ctx.clone();
            let (combined, typ) = match &mut *self.s {
                SNode::Decl(e1, t1, e2) => {
                    let var_name = match &*e1.e {
                        ENode::Variable(name) => name.clone(),
                        _ => return Err(UnificationError { pos: None, message: format!("Expected a variable name in declaration, got {:?}", *e1.e) }),
                    };
                    if TypeContext::is_builtin(&var_name) {
                        return Err(UnificationError { pos: None, message: format!("Redefinition of builtin function '{}' not allowed", var_name) });
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
        })();
        result.map_err(|e| e.with_pos(self.pos.clone()))
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

#[derive(Debug, Clone)]
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

impl PartialEq for Expr {
    /// Structural equality; `pos` is metadata and deliberately excluded.
    fn eq(&self, other: &Self) -> bool {
        self.e == other.e && self.ctx == other.ctx && self.typ == other.typ
    }
}

impl Expr {
    pub fn from(node : ENode) -> Expr {
        Self::at(Pos::nil(), node)
    }

    pub fn at(pos : Pos, node : ENode) -> Expr {
        Expr {
            e : Box::new(node),
            ctx : TypeContext::new(),
            pos,
            typ : Monotype::infer(),
        }
    }
}

/// Fill every `Pos` reachable from `stmt` with line/column data derived from
/// the buffer's line index (the grammar records raw byte offsets).
pub fn fill_stmt_positions(stmt : &mut Stmt, index : &LineIndex) {
    if !stmt.pos.is_nil() {
        stmt.pos.fill(index);
    }
    match &mut *stmt.s {
        SNode::Decl(e1, _, e2) => {
            fill_expr_positions(e1, index);
            fill_expr_positions(e2, index);
        },
        SNode::Expr(e1) => fill_expr_positions(e1, index),
        SNode::TypeDecl(_, _) => {}
    }
}

fn fill_expr_positions(expr : &mut Expr, index : &LineIndex) {
    if !expr.pos.is_nil() {
        expr.pos.fill(index);
    }
    match &mut *expr.e {
        ENode::Variable(_) | ENode::Literal(_) => {}
        ENode::Abstraction(_, body) => fill_expr_positions(body, index),
        ENode::Application(f, x) => {
            fill_expr_positions(f, index);
            fill_expr_positions(x, index);
        },
        ENode::Let(_, e1, e2) => {
            fill_expr_positions(e1, index);
            fill_expr_positions(e2, index);
        },
        ENode::IfElse(c, t, e) => {
            fill_expr_positions(c, index);
            fill_expr_positions(t, index);
            fill_expr_positions(e, index);
        },
        ENode::Block(stmts, e) => {
            for s in stmts.iter_mut() {
                fill_stmt_positions(s, index);
            }
            fill_expr_positions(e, index);
        },
        ENode::Comparison(_, a, b) => {
            fill_expr_positions(a, index);
            fill_expr_positions(b, index);
        },
        ENode::Arithmetic(_, a, b) => {
            fill_expr_positions(a, index);
            fill_expr_positions(b, index);
        },
        ENode::Logical(_, a, b) => {
            fill_expr_positions(a, index);
            fill_expr_positions(b, index);
        },
        ENode::Unary(_, e) => fill_expr_positions(e, index),
        ENode::List(es) => {
            for e in es.iter_mut() {
                fill_expr_positions(e, index);
            }
        },
        ENode::Cons(h, t) => {
            fill_expr_positions(h, index);
            fill_expr_positions(t, index);
        },
        ENode::Match(scrut, cases) => {
            fill_expr_positions(scrut, index);
            for c in cases.iter_mut() {
                fill_expr_positions(&mut c.val, index);
                fill_expr_positions(&mut c.exp, index);
            }
        },
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
    pub ctx : TypeContext,
    /// The name of the source this program was parsed from (file path, or
    /// `"<repl>"`), used when attaching locations to generated MLIR.
    pub source_name : String
}

impl Program {
    pub fn parse(buf : &str) -> Result<Box<Program>, String> {
        let mut program = grammar::ProgParser::new().parse(buf).map_err(|e| format!("{}", e))?;
        let index = LineIndex::new(buf);
        for stmt in program.stmts.iter_mut() {
            fill_stmt_positions(stmt, &index);
        }
        Ok(program)
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
