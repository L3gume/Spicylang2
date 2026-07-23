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
 *
 *  TODO: Type inference rules for other expressions
 */
use std::collections::HashMap;

use crate::ast::{Expr, Type};
use crate::ast::Expr::*;


#[derive(Debug, Clone, PartialEq)]
pub enum TypeFunction {
    Unit,
    Int,
    Float,
    Bool,
    Str,
    Fn, // ->
    List,
}

#[derive(Debug, Clone, PartialEq)]
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
                    _ => Self::TypeVariable(name),
                },
            Self::TypeFuncApplication(typ_fn, types) =>
                Self::TypeFuncApplication(typ_fn, types.iter().map(|typ| typ.apply(sub)).collect())
        }
    }

    pub fn instantiate(&self, mappings : &mut HashMap<String, Monotype>) -> Monotype {
        match self {
            Self::TypeVariable(var) => match mappings.get(var) {
                Some(monotype) => monotype.clone(),
                _ => self.clone()
            },
            Self::TypeFuncApplication(func, types) => 
                Self::TypeFuncApplication(func.clone(), types.iter().map(|typ| typ.instantiate(mappings)).collect())
        }
    }
}

#[derive(Debug, Clone)]
pub enum Polytype {
    Mono(Box<Monotype>),
    TypeQuantifier(String, Box<Polytype>),
}

impl Polytype {
    pub fn apply(&self, sub : &Substitution) -> Polytype {
        match self.clone() {
            Self::Mono(mono) => Self::Mono(Box::new(mono.apply(sub))),
            Self::TypeQuantifier(s, poly) => Self::TypeQuantifier(s, Box::new(poly.apply(sub))),
        }
    }

    pub fn instantiate(&self, ctx : &mut TypeContext, mappings : &mut HashMap<String, Monotype>) -> Monotype {
        match self {
            Self::Mono(mon) => mon.instantiate(mappings),
            Self::TypeQuantifier(quant, typ) => {
                mappings.insert(quant.clone(), Monotype::TypeVariable(ctx.new_typevar()));
                typ.instantiate(ctx, mappings)
            }
        }
    }
}


#[derive(Debug)]
pub struct TypeContext {
    type_var_ctr : u32,
    pub variables : HashMap<String, Polytype>
}

impl TypeContext {
    pub fn new() -> TypeContext {
        TypeContext { type_var_ctr : 0, variables : HashMap::new() }
    }

    pub fn make(map: HashMap<String, Polytype>) -> TypeContext {
        TypeContext { type_var_ctr : 0, variables : map }
    }

    pub fn apply(&self, sub : &Substitution) -> TypeContext {
        TypeContext { type_var_ctr: self.type_var_ctr, variables: self.variables.iter().map(|(k, t)| (k.clone(), t.apply(sub))).collect() }
    }

    pub fn new_typevar(&mut self) -> String {
        let ret = format!("t{}", self.type_var_ctr);
        self.type_var_ctr += 1;
        ret
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

    pub fn make(map: HashMap<String, Monotype>) -> Substitution {
        Substitution { variables : map }
    }

    pub fn combine(&self, s2 : &Substitution) -> Substitution {
        let mut applied: HashMap<String, Monotype> = s2.variables.iter()
            .map(|(k, mon)| (k.clone(), mon.apply(self)))
            .collect();
        for (k, mon) in &self.variables {
            if !s2.variables.contains_key(k) {
                applied.insert(k.clone(), mon.clone());
            }
        }
        Substitution::make(applied)
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

pub fn instantiate(typ : &Monotype) -> Monotype {
    todo!()
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

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Monotype {
        Monotype::TypeVariable(name.to_string())
    }

    fn int() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunction::Int), vec![])
    }

    fn bool() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunction::Bool), vec![])
    }

    fn fn_type(arg: Monotype, ret: Monotype) -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunction::Fn), vec![arg, ret])
    }

    fn sub(pairs: Vec<(&str, Monotype)>) -> Substitution {
        Substitution::make(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    #[test]
    fn combine_empty_both() {
        let s1 = sub(vec![]);
        let s2 = sub(vec![]);
        let result = s1.combine(&s2);
        assert!(result.variables.is_empty());
    }

    #[test]
    fn combine_empty_s1() {
        let s1 = sub(vec![]);
        let s2 = sub(vec![("x", int())]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 1);
        assert_eq!(result.variables.get("x"), Some(&int()));
    }

    #[test]
    fn combine_empty_s2() {
        let s1 = sub(vec![("x", int())]);
        let s2 = sub(vec![]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 1);
        assert_eq!(result.variables.get("x"), Some(&int()));
    }

    #[test]
    fn combine_disjoint() {
        let s1 = sub(vec![("a", int())]);
        let s2 = sub(vec![("b", bool())]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 2);
        assert_eq!(result.variables.get("a"), Some(&int()));
        assert_eq!(result.variables.get("b"), Some(&bool()));
    }

    #[test]
    fn combine_overlapping() {
        let s1 = sub(vec![("x", int())]);
        let s2 = sub(vec![("x", bool())]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 1);
        assert_eq!(result.variables.get("x"), Some(&bool()));
    }

    #[test]
    fn combine_s2_chained_through_s1() {
        let s1 = sub(vec![("x", int())]);
        let s2 = sub(vec![("y", var("x"))]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 2);
        assert_eq!(result.variables.get("x"), Some(&int()));
        assert_eq!(result.variables.get("y"), Some(&int()));
    }

    #[test]
    fn combine_function_type_through_s1() {
        let s1 = sub(vec![("x", var("y"))]);
        let s2 = sub(vec![("z", fn_type(bool(), var("x")))]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 2);
        assert_eq!(result.variables.get("x"), Some(&var("y")));
        assert_eq!(result.variables.get("z"), Some(&fn_type(bool(), var("y"))));
    }

    #[test]
    fn combine_multi_chain() {
        let s1 = sub(vec![("a", int()), ("b", var("a"))]);
        let s2 = sub(vec![("b", bool()), ("c", var("b"))]);
        let result = s1.combine(&s2);
        assert_eq!(result.variables.len(), 3);
        assert_eq!(result.variables.get("a"), Some(&int()));
        assert_eq!(result.variables.get("b"), Some(&bool()));
        assert_eq!(result.variables.get("c"), Some(&var("a")));
    }

    #[test]
    fn new_typevar_sequential() {
        let mut ctx = TypeContext::new();
        assert_eq!(ctx.new_typevar(), "t0");
        assert_eq!(ctx.new_typevar(), "t1");
        assert_eq!(ctx.new_typevar(), "t2");
        assert_eq!(ctx.new_typevar(), "t3");
    }

    #[test]
    fn new_typevar_independent_contexts() {
        let mut ctx1 = TypeContext::new();
        let mut ctx2 = TypeContext::new();
        assert_eq!(ctx1.new_typevar(), "t0");
        assert_eq!(ctx2.new_typevar(), "t0");
        assert_eq!(ctx1.new_typevar(), "t1");
        assert_eq!(ctx2.new_typevar(), "t1");
    }

    fn mono(m: Monotype) -> Polytype {
        Polytype::Mono(Box::new(m))
    }

    fn forall(var: &str, body: Polytype) -> Polytype {
        Polytype::TypeQuantifier(var.to_string(), Box::new(body))
    }

    fn mappings(pairs: Vec<(&str, Monotype)>) -> HashMap<String, Monotype> {
        pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect()
    }

    #[test]
    fn polytype_instantiate_mono_no_quantifiers() {
        let p = mono(int());
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), int());
    }

    #[test]
    fn polytype_instantiate_mono_unmapped_var() {
        let p = mono(var("a"));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), var("a"));
    }

    #[test]
    fn polytype_instantiate_mono_mapped_var() {
        let p = mono(var("a"));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![("a", int())]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), int());
    }

    #[test]
    fn polytype_instantiate_single_quantifier() {
        let p = forall("a", mono(fn_type(var("a"), int())));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), fn_type(var("t0"), int()));
    }

    #[test]
    fn polytype_instantiate_nested_quantifiers() {
        let p = forall("a", forall("b", mono(fn_type(var("a"), var("b")))));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), fn_type(var("t0"), var("t1")));
    }

    #[test]
    fn polytype_instantiate_unused_quantifier() {
        let p = forall("a", mono(int()));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), int());
    }

    #[test]
    fn polytype_instantiate_repeated_quantifier() {
        let p = forall("a", mono(fn_type(var("a"), var("a"))));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), fn_type(var("t0"), var("t0")));
    }

    #[test]
    fn polytype_instantiate_quantifier_function() {
        let p = forall("a", mono(fn_type(var("a"), bool())));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, &mut map), fn_type(var("t0"), bool()));
    }
}
