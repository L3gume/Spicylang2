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
 * If-Then-Else expr:
 *
 *   Γ ⊢ e₀ : Bool    Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ
 *  ---------------------------------------------
 *          Γ ⊢ if e₀ then e₁ else e₂ : τ
 *
 *  If it follows from context Γ that e₀ has type Bool and that e₁ and e₂ have type τ.
 *  Then
 *  It follows from context Γ that expr if e₀ then e₁ else e₂ has type τ
 *
 * Literal expr:
 *
 *   ─────────────
 *   Γ ⊢ lit : τ(lit)
 *
 *  Where τ(lit) is the literal's fixed type — Int, Float, Bool, Str, or Unit.
 *  Literals are axioms: they contribute no premises and type independently of Γ.
 *  They constrain other rules by forcing unification with their concrete type.
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
 */
use std::collections::HashMap;

use crate::ast::{Binding, Expr, Lit, Type};
use crate::ast::Expr::*;
use crate::types::Monotype::TypeFuncApplication;


#[derive(Debug, Clone, PartialEq)]
pub enum TypeFunc {
    Infer,
    Unit,
    Int,
    Float,
    Bool,
    Str,
    Fn, // ->
    List,
    Enum(String)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Monotype {
    TypeVariable(String),
    TypeFuncApplication(Box<TypeFunc>, Vec<Monotype>),
}

impl Monotype {
    pub fn default() -> Monotype {
        Self::TypeVariable(String::new())
    }

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

    pub fn free_variables(&self) -> Vec<String> {
        match self {
            Self::TypeVariable(v) => vec![v.clone()],
            Self::TypeFuncApplication(_, ts) => ts.iter().flat_map(|t| t.free_variables()).collect()
        }
    }

    pub fn contains(&self, typ : &Monotype) -> bool {
        match typ {
            Self::TypeVariable(v) => match self {
                Self::TypeVariable(v2) => v == v2,
                Self::TypeFuncApplication(_, ts) => ts.iter().any(|t| t.contains(typ))
            },
            Self::TypeFuncApplication(_, _) => false
        }
    }

    pub fn infer() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Infer), vec![])
    }

    pub fn bool() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Bool), vec![])
    }

    pub fn int() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Int), vec![])
    }

    pub fn float() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Float), vec![])
    }

    pub fn string() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Str), vec![])
    }

    pub fn unit() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Unit), vec![])
    }

    pub fn func(vars : Vec<Monotype>) -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Fn), vars)
    }

    pub fn list(vars : Vec<Monotype>) -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::List), vars)
    }
}

#[derive(Debug, Clone, PartialEq)]
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

    pub fn instantiate(&self, ctx : &mut TypeContext, mappings : Option<HashMap<String, Monotype>>) -> Monotype {
        let mut maps = mappings.unwrap_or(HashMap::new());
        match self {
            Self::Mono(mon) => mon.instantiate(&mut maps),
            Self::TypeQuantifier(quant, typ) => {
                maps.insert(quant.clone(), Monotype::TypeVariable(ctx.new_typevar()));
                typ.instantiate(ctx, Some(maps))
            }
        }
    }

    pub fn free_variables(&self) -> Vec<String> {
        match self {
            Self::Mono(mon) => mon.free_variables(),
            Self::TypeQuantifier(quant, typ) =>
                typ.free_variables().into_iter().filter(|n| n != quant).collect()
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
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

    pub fn combine(&self, s2 : Substitution) -> Substitution {
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

#[derive(Debug, Clone)]
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

    pub fn get(&self, name : &String) -> Option<Polytype> {
        self.variables.get(name).cloned()
    }

    pub fn add(&mut self, name : String, typ : Polytype) {
        self.variables.insert(name, typ);
    }

    pub fn apply(&self, sub : &Substitution) -> TypeContext {
        TypeContext { type_var_ctr: self.type_var_ctr, variables: self.variables.iter().map(|(k, t)| (k.clone(), t.apply(sub))).collect() }
    }

    pub fn new_typevar(&mut self) -> String {
        let ret = format!("t{}", self.type_var_ctr);
        self.type_var_ctr += 1;
        ret
    }

    pub fn free_variables(&self) -> Vec<String> {
        self.variables.values().flat_map(|t| t.free_variables()).collect()
    }

    pub fn generalise(&self, typ : &Monotype) -> Polytype {
        let quants = diff(typ.free_variables(), self.free_variables());
        let mut poly = Polytype::Mono(Box::new(typ.clone()));
        for q in quants {
            poly = Polytype::TypeQuantifier(q, Box::new(poly));
        }
        poly
    }
}

pub fn unify(typ1 : &Monotype, typ2 : &Monotype) -> Result<Substitution, UnificationError> {
    match typ1 {
        Monotype::TypeVariable(v1) => match typ2 {
            Monotype::TypeVariable(v2) =>
                if v1 == v2 {
                    Ok(Substitution::new())
                } else {
                    if typ2.contains(typ1) {
                        Err(UnificationError { message: "Infinite recursive type".to_string() })
                    } else {
                        Ok(Substitution::make(HashMap::from([(v1.clone(), typ2.clone())])))
                    }
                },
            _ => if typ2.contains(typ1) {
                    Err(UnificationError { message: "Infinite recursive type".to_string() })
                } else {
                    Ok(Substitution::make(HashMap::from([(v1.clone(), typ2.clone())])))
                }
        }
        Monotype::TypeFuncApplication(f1, ts1) => match typ2 {
            Monotype::TypeVariable(_) => unify(typ2, typ1),
            Monotype::TypeFuncApplication(f2, ts2 ) =>
                if f1 != f2 {
                    Err(UnificationError { message: format!("Type function application mismatch: {:?} != {:?}", f1, f2) })
                } else {
                    if ts1.len() != ts2.len() {
                        Err(UnificationError { message: format!("Type functions have different number of args: {:?}, {:?}", ts1, ts2) })
                    } else {
                        let mut sub = Substitution::new();
                        for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                            sub = sub.combine(unify(&t1.apply(&sub), &t2.apply(&sub))?);
                        }
                        Ok(sub)
                    }
                }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct UnificationError {
    pub message : String
    // TODO: location information?
}


fn diff<T>(v1 : Vec<T>, v2 : Vec<T>) -> Vec<T> where T : PartialEq + Clone {
    v1.into_iter().filter(|x| !v2.contains(x)).collect()
}

pub fn type_to_typefn(typ : &Type, context : &mut TypeContext) -> Monotype {
    match &typ.t {
        Monotype::TypeFuncApplication(func, _) if **func == TypeFunc::Infer
            => Monotype::TypeVariable(context.new_typevar()),
        _ => typ.t.clone()
    }
}

pub fn algo_w(context : &mut TypeContext, expr : &Expr) -> Result<(Substitution, Monotype), UnificationError> {
    match expr {
        Variable(name) => match context.get(name) {
            Some(poly) => {
                Ok((Substitution::new(), poly.instantiate(context, None)))
            }
            _ => Err(UnificationError { message: format!("Undefined variable {}!", name) } )
        },
        Abstraction(bind, exp) => {
            let Binding(name, typp) = &**bind;
            let beta_mon = type_to_typefn(&typp, context);
            let beta_poly = Polytype::Mono(Box::new(beta_mon.clone()));
            context.add(name.clone(), beta_poly);
            let (sub1, t1) = algo_w(context, exp)?;
            let beta = Monotype::TypeFuncApplication(Box::new(TypeFunc::Fn), vec!(beta_mon, t1)).apply(&sub1);
            Ok((sub1, beta))
        },
        Application(exp1, exp2) => {
            let (s1, t1) = algo_w(context, exp1)?;
            *context = context.apply(&s1);
            let (s2, t2) = algo_w(context, exp2)?;
            let beta = TypeFuncApplication(Box::new(TypeFunc::Fn), vec!(t2, Monotype::TypeVariable(context.new_typevar())));
            let s3 = unify(&t1.apply(&s2), &beta)?;
            Ok((s1.combine(s2).combine(s3.clone()), beta.apply(&s3)))
        },
        Let(name, exp1, exp2) => {
            let (s1, t1) = algo_w(context, exp1)?;
            *context = context.apply(&s1);
            context.add(name.clone(), context.generalise(&t1));
            let (s2, t2) = algo_w(context, exp2)?;
            Ok((s1.combine(s2), t2))
        }
        IfElse(cond, exp1, exp2) => {
            let (s1, t1) = algo_w(context, cond)?;
            let s2 = unify(&t1, &Monotype::bool())?;
            *context = context.apply(&s1).apply(&s2);
            let (s3, t3) = algo_w(context, exp1)?;
            *context = context.apply(&s3);
            let (s4, t4) = algo_w(context, exp2)?;
            let s5 = unify(&t3.apply(&s4), &t4)?;
            Ok((
                s1.combine(s2).combine(s3).combine(s4.clone()).combine(s5.clone()),
                t3.apply(&s4).apply(&s5)
            ))
        },
        Literal(lit) => {
            let typ = match lit.as_ref() {
                Lit::Int(_) => Monotype::int(),
                Lit::Bool(_) => Monotype::bool(),
                Lit::Str(_) => Monotype::string(),
                Lit::Float(_) => Monotype::float(),
                Lit::Unit => Monotype::unit(),
            };
            Ok((Substitution::new(), typ))
        }
    }
}

// TODO: Second arg is expr
pub fn algo_m(context : &TypeContext, expr : &Expr, typ : &TypeFunc) -> Substitution {
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
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Int), vec![])
    }

    fn bool() -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Bool), vec![])
    }

    fn fn_type(arg: Monotype, ret: Monotype) -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Fn), vec![arg, ret])
    }

    fn sub(pairs: Vec<(&str, Monotype)>) -> Substitution {
        Substitution::make(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    #[test]
    fn combine_empty_both() {
        let s1 = sub(vec![]);
        let s2 = sub(vec![]);
        let result = s1.combine(s2);
        assert!(result.variables.is_empty());
    }

    #[test]
    fn combine_empty_s1() {
        let s1 = sub(vec![]);
        let s2 = sub(vec![("x", int())]);
        let result = s1.combine(s2);
        assert_eq!(result.variables.len(), 1);
        assert_eq!(result.variables.get("x"), Some(&int()));
    }

    #[test]
    fn combine_empty_s2() {
        let s1 = sub(vec![("x", int())]);
        let s2 = sub(vec![]);
        let result = s1.combine(s2);
        assert_eq!(result.variables.len(), 1);
        assert_eq!(result.variables.get("x"), Some(&int()));
    }

    #[test]
    fn combine_disjoint() {
        let s1 = sub(vec![("a", int())]);
        let s2 = sub(vec![("b", bool())]);
        let result = s1.combine(s2);
        assert_eq!(result.variables.len(), 2);
        assert_eq!(result.variables.get("a"), Some(&int()));
        assert_eq!(result.variables.get("b"), Some(&bool()));
    }

    #[test]
    fn combine_overlapping() {
        let s1 = sub(vec![("x", int())]);
        let s2 = sub(vec![("x", bool())]);
        let result = s1.combine(s2);
        assert_eq!(result.variables.len(), 1);
        assert_eq!(result.variables.get("x"), Some(&bool()));
    }

    #[test]
    fn combine_s2_chained_through_s1() {
        let s1 = sub(vec![("x", int())]);
        let s2 = sub(vec![("y", var("x"))]);
        let result = s1.combine(s2);
        assert_eq!(result.variables.len(), 2);
        assert_eq!(result.variables.get("x"), Some(&int()));
        assert_eq!(result.variables.get("y"), Some(&int()));
    }

    #[test]
    fn combine_function_type_through_s1() {
        let s1 = sub(vec![("x", var("y"))]);
        let s2 = sub(vec![("z", fn_type(bool(), var("x")))]);
        let result = s1.combine(s2);
        assert_eq!(result.variables.len(), 2);
        assert_eq!(result.variables.get("x"), Some(&var("y")));
        assert_eq!(result.variables.get("z"), Some(&fn_type(bool(), var("y"))));
    }

    #[test]
    fn combine_multi_chain() {
        let s1 = sub(vec![("a", int()), ("b", var("a"))]);
        let s2 = sub(vec![("b", bool()), ("c", var("b"))]);
        let result = s1.combine(s2);
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

    fn ctx_map(pairs: Vec<(&str, Polytype)>) -> HashMap<String, Polytype> {
        pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect()
    }

    #[test]
    fn polytype_instantiate_mono_no_quantifiers() {
        let p = mono(int());
        let mut ctx = TypeContext::new();
        let map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), int());
    }

    #[test]
    fn polytype_instantiate_mono_unmapped_var() {
        let p = mono(var("a"));
        let mut ctx = TypeContext::new();
        let map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), var("a"));
    }

    #[test]
    fn polytype_instantiate_mono_mapped_var() {
        let p = mono(var("a"));
        let mut ctx = TypeContext::new();
        let map = mappings(vec![("a", int())]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), int());
    }

    #[test]
    fn polytype_instantiate_single_quantifier() {
        let p = forall("a", mono(fn_type(var("a"), int())));
        let mut ctx = TypeContext::new();
        let map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), fn_type(var("t0"), int()));
    }

    #[test]
    fn polytype_instantiate_nested_quantifiers() {
        let p = forall("a", forall("b", mono(fn_type(var("a"), var("b")))));
        let mut ctx = TypeContext::new();
        let map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), fn_type(var("t0"), var("t1")));
    }

    #[test]
    fn polytype_instantiate_unused_quantifier() {
        let p = forall("a", mono(int()));
        let mut ctx = TypeContext::new();
        let map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), int());
    }

    #[test]
    fn polytype_instantiate_repeated_quantifier() {
        let p = forall("a", mono(fn_type(var("a"), var("a"))));
        let mut ctx = TypeContext::new();
        let map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), fn_type(var("t0"), var("t0")));
    }

    #[test]
    fn polytype_instantiate_quantifier_function() {
        let p = forall("a", mono(fn_type(var("a"), bool())));
        let mut ctx = TypeContext::new();
        let mut map = mappings(vec![]);
        assert_eq!(p.instantiate(&mut ctx, Some(map)), fn_type(var("t0"), bool()));
    }

    #[test]
    fn generalise_no_vars_in_type() {
        let ctx = TypeContext::make(ctx_map(vec![("x", mono(int()))]));
        assert_eq!(ctx.generalise(&int()), mono(int()));
    }

    #[test]
    fn generalise_single_var_not_in_context() {
        let ctx = TypeContext::new();
        assert_eq!(ctx.generalise(&var("a")), forall("a", mono(var("a"))));
    }

    #[test]
    fn generalise_single_var_in_context() {
        let ctx = TypeContext::make(ctx_map(vec![("x", mono(fn_type(var("a"), int())))]));
        assert_eq!(ctx.generalise(&var("a")), mono(var("a")));
    }

    #[test]
    fn generalise_fn_some_vars_in_context() {
        let ctx = TypeContext::make(ctx_map(vec![("x", mono(fn_type(var("a"), int())))]));
        assert_eq!(
            ctx.generalise(&fn_type(var("a"), var("b"))),
            forall("b", mono(fn_type(var("a"), var("b"))))
        );
    }

    #[test]
    fn generalise_fn_no_vars_in_context() {
        let ctx = TypeContext::new();
        assert_eq!(
            ctx.generalise(&fn_type(var("a"), var("b"))),
            forall("b", forall("a", mono(fn_type(var("a"), var("b")))))
        );
    }

    #[test]
    fn generalise_fn_all_vars_in_context() {
        let ctx = TypeContext::make(ctx_map(vec![
            ("x", mono(fn_type(var("a"), var("b")))),
        ]));
        assert_eq!(
            ctx.generalise(&fn_type(var("a"), var("b"))),
            mono(fn_type(var("a"), var("b")))
        );
    }

    fn ok(sub_pairs: Vec<(&str, Monotype)>) -> Result<Substitution, UnificationError> {
        Ok(sub(sub_pairs))
    }

    fn err(msg: &str) -> Result<Substitution, UnificationError> {
        Err(UnificationError { message: msg.to_string() })
    }

    #[test]
    fn unify_same_var() {
        assert_eq!(unify(&var("a"), &var("a")), ok(vec![]));
    }

    #[test]
    fn unify_diff_vars() {
        assert_eq!(unify(&var("a"), &var("b")), ok(vec![("a", var("b"))]));
    }

    #[test]
    fn unify_var_and_concrete() {
        assert_eq!(unify(&var("a"), &int()), ok(vec![("a", int())]));
    }

    #[test]
    fn unify_concrete_and_var() {
        assert_eq!(unify(&int(), &var("a")), ok(vec![("a", int())]));
    }

    #[test]
    fn unify_same_concrete() {
        assert_eq!(unify(&int(), &int()), ok(vec![]));
    }

    #[test]
    fn unify_different_concretes() {
        let result = unify(&int(), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn unify_infinite_type() {
        let result = unify(&var("a"), &fn_type(var("a"), int()));
        assert!(result.is_err());
    }

    #[test]
    fn unify_infinite_nested() {
        let result = unify(&var("a"), &fn_type(int(), var("a")));
        assert!(result.is_err());
    }

    #[test]
    fn unify_fn_same_structure() {
        assert_eq!(
            unify(&fn_type(var("a"), int()), &fn_type(var("b"), int())),
            ok(vec![("a", var("b"))])
        );
    }

    #[test]
    fn unify_fn_chain_substitution() {
        assert_eq!(
            unify(&fn_type(var("a"), int()), &fn_type(int(), var("b"))),
            ok(vec![("a", int()), ("b", int())])
        );
    }

    #[test]
    fn unify_fn_different_constructors() {
        let result = unify(&fn_type(int(), int()), &fn_type(int(), bool()));
        assert!(result.is_err());
    }
}
