/*
 * Type unification algo
 *
 * unify(a: Monotype, b: Monotype) => Substitution:
 *   if a is typevar:
 *     if b is same typevar:
 *       return {}
 *     if b contains a:
 *       Error("infinite type")
 *     return {a |-> b}
 *
 *   if b is typevar:
 *     return unify(b, a)
 *
 *   if a & b both typefunvappl:
 *     if a & b have different type funcs:
 *       Error("Different functions")
 *     let S = {}
 *     for i in range(num of type func arguments):
 *       S = combine(S, unify(S(a.args[i]), S(b.args[i])))
 *     return S
 *
 *   Error(?)
 *
 *
 *
 *
 * Variable:
 *
 *   x : σ ∈ Γ      if variable x of polytype σ is in the typing context
 * --------------   then
 *   Γ ⊢ x : σ      from Γ it follows that (⊢) x is of type σ
 *
 * Application:
 *
 *   Γ ⊢ e₀ : τₐ → τᵦ    Γ ⊢ e₁ : τₐ
 * -----------------------------------
 *           Γ ⊢ e₀ e₁ : τᵦ
 *
 * If it follows from Γ that e₀ is of polytype τₐ → τᵦ and e₁ is of polytype τₐ
 * then
 * From Γ it follows that application of e₀ and e₁ is of polytype τᵦ
 *
 * Abstraction:
 *
 *   Γ, x : τₐ ⊢ e : τᵦ
 * ----------------------  
 *   Γ ⊢ λx → e : τₐ → τᵦ
 *
 * if it follows from the context plus a variable x of type τₐ that expression e has type τᵦ
 * Then
 * From the context it follows that function definition \x -> e defines a function of type τₐ → τᵦ
 *
 * Let-binding expr:
 *
 *   Γ ⊢ e₀ : σ   Γ, x : σ ⊢ e₁ : τ
 *  --------------------------------
 *       Γ ⊢ let x = e₀ in e₁ : τ
 *
 *  If it follows from Context that e₀ has type σ and if also follows from context plus a variable x
 *  of type σ that expression e₁ has type τ
 *  then
 *  it follows from context that expression 'let x = e₀ in e₁' has type τ
 *
 *  Let bindings have type of last expression
 *
 * Instantiation:
 *
 *  Γ ⊢ e : σₐ    σₐ ⊑ σᵦ
 * -----------------------
 *      Γ ⊢ e : σᵦ
 *
 *  If if follows from context that the e has type σₐ and σₐ more general than σᵦ
 *  then
 *  It follows from context that e has type σᵦ
 *
 *  ie: if e has type σₐ : ∀α. λInt → α and σᵦ : λInt → Bool, then e also has type λInt → Bool
 *
 * Generalisation:
 *
 *  Γ ⊢ e : σ   α ∉ FV(Γ)
 * -----------------------
 *      Γ ⊢ e : ∀α. σ
 *
 *  If it follows from context that expression e is of polytype σ and that type var α is not a free
 *  variable in the context
 *  then
 *  It follows from context that expression e is of polytype ∀α. σ (this means α can be anything)
 */
use std::collections::HashMap;

use crate::ast::{Expr, Type};
use crate::ast::Expr::*;


#[derive(Debug, Clone)]
pub enum TypeFunction {
    Unit,
    Int,
    Float,
    Bool,
    Str,
    Fn, // ->
    List,
}

#[derive(Debug, Clone)]
pub enum Monotype {
    TypeVariable(String),
    TypeFuncApplication(Box<TypeFunction>, Vec<Monotype>),
}

impl Monotype {
    pub fn apply(&self, sub : &Substitution) -> Monotype {
        match self.clone() {
            Self::TypeVariable(name) =>
                match sub.variables.get(&name) {
                    Some(monotype) => monotype.clone(),
                    None => Self::TypeVariable(name),
                },
            Self::TypeFuncApplication(typ_fn, types) =>
                Self::TypeFuncApplication(typ_fn, types.iter().map(|typ| typ.apply(sub)).collect())
        }
    }
}

#[derive(Debug, Clone)]
pub enum Polytype {
    Monotype(Box<Monotype>),
    TypeQuantifier(String, Box<Polytype>),
}

impl Polytype {
    pub fn apply(&self, sub : &Substitution) -> Polytype {
        match self.clone() {
            Self::Monotype(mono) => Self::Monotype(Box::new(mono.apply(sub))),
            Self::TypeQuantifier(s, poly) => Self::TypeQuantifier(s, Box::new(poly.apply(sub))),
        }
    }
}

#[derive(Debug)]
pub struct TypeContext {
    pub variables : HashMap<String, Polytype>
}

impl TypeContext {
    pub fn new() -> TypeContext {
        TypeContext { variables : HashMap::new() }
    }

    pub fn apply(&self, sub : &Substitution) -> TypeContext {
        TypeContext { variables: self.variables.iter().map(|(k, t)| (k.clone(), t.apply(sub))).collect() }
    }
}

#[derive(Debug)]
pub struct Substitution {
    pub variables : HashMap<String, Monotype>
}

impl Substitution {
    pub fn new() -> Substitution {
        Substitution { variables: HashMap::new() }
    }

    pub fn combine(&self, s2 : &Substitution) -> Substitution {
        // TODO: Implement
        Substitution::new()
    }
}

#[derive(Debug)]
pub struct UnificationError {
    pub message : String
    // TODO: location information?
}

pub fn unify(typ1 : &Monotype, typ2 : &Monotype) -> Result<Substitution, UnificationError> {
    // TODO: Implement
    Ok(Substitution::new())
}

pub fn instantiate() {
    // TODO: Implement
}

pub fn generalise() {
    // TODO: Implement
}

// TODO: Second arg is expr
pub fn algo_w(context : &TypeContext, expr : &Expr) -> Substitution {
    // TODO: Implement
    match expr {
        Variable(name) => Substitution::new(),
        Abstraction(bind, exp) => Substitution::new(),
        Application(exp1, exp2) => Substitution::new(),
        Let(name, exp1, exp2) => Substitution::new(),
        Literal(lit) => Substitution::new(),
        IfElse(cond, exp1, exp2) => Substitution::new(),
    }
}

// TODO: Second arg is expr
pub fn algo_m(context : &TypeContext, expr : &Expr, typ : &Type) -> Substitution {
    // TODO: Implement
    match expr {
        Variable(name) => Substitution::new(),
        Abstraction(bind, exp) => Substitution::new(),
        Application(exp1, exp2) => Substitution::new(),
        Let(name, exp1, exp2) => Substitution::new(),
        Literal(lit) => Substitution::new(),
        IfElse(cond, exp1, exp2) => Substitution::new(),
    }
}
