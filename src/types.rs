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
use std::collections::{HashMap, HashSet};

use crate::ast::*;
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
    Enum(String) // TODO: might have to go
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
                    Some(monotype) => monotype.apply(sub),
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

    pub fn var(name : String) -> Monotype {
        Self::TypeVariable(name)
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

    pub fn enum_type(name : String) -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Enum(name)), vec![])
    }

    pub fn enum_app(name : String, vars : Vec<Monotype>) -> Monotype {
        Monotype::TypeFuncApplication(Box::new(TypeFunc::Enum(name)), vars)
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
        let mut maps = mappings.unwrap_or_default();
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeAlias {
    pub params : Vec<String>,
    pub rhs : Monotype,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeContext {
    type_var_ctr : u32,
    pub variables : HashMap<String, Polytype>,
    type_aliases : HashMap<String, TypeAlias>,
    enum_names : HashSet<String>
}

impl TypeContext {
    pub fn new() -> TypeContext {
        TypeContext { type_var_ctr : 0, variables : HashMap::new(), type_aliases : HashMap::new(), enum_names : HashSet::new() }
    }

    pub fn make(map: HashMap<String, Polytype>) -> TypeContext {
        TypeContext { type_var_ctr : 0, variables : map, type_aliases : HashMap::new(), enum_names : HashSet::new() }
    }

    pub fn get(&self, name : &String) -> Option<Polytype> {
        self.variables.get(name).cloned()
    }

    pub fn add(&mut self, name : String, typ : Polytype) {
        self.variables.insert(name, typ);
    }

    pub fn remove(&mut self, name : &str) {
        self.variables.remove(name);
    }

    pub fn add_alias(&mut self, name : String, alias : TypeAlias) {
        self.type_aliases.insert(name, alias);
    }

    pub fn get_alias(&self, name : &str) -> Option<&TypeAlias> {
        self.type_aliases.get(name)
    }

    pub fn add_enum_name(&mut self, name : String) {
        self.enum_names.insert(name);
    }

    pub fn has_enum_name(&self, name : &str) -> bool {
        self.enum_names.contains(name)
    }

    pub fn apply(&self, sub : &Substitution) -> TypeContext {
        TypeContext { type_var_ctr: self.type_var_ctr, variables: self.variables.iter().map(|(k, t)| (k.clone(), t.apply(sub))).collect(), type_aliases: self.type_aliases.clone(), enum_names: self.enum_names.clone() }
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
                    Err(UnificationError { message: format!("Type function application mismatch: {:?} != {:?} (full: {:?} vs {:?})", f1, f2, typ1, typ2) })
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

impl std::fmt::Display for UnificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}


fn diff<T>(v1 : Vec<T>, v2 : Vec<T>) -> Vec<T> where T : PartialEq + Clone {
    v1.into_iter().filter(|x| !v2.contains(x)).collect()
}

fn expand(typ : &Monotype, context : &mut TypeContext, visited : &mut Vec<String>) -> Result<Monotype, UnificationError> {
    match typ {
        Monotype::TypeVariable(_) => Ok(typ.clone()),
        Monotype::TypeFuncApplication(func, args) => {
            let mut expanded_args : Vec<Monotype> = Vec::new();
            for arg in args {
                expanded_args.push(expand(arg, context, visited)?);
            }
            match &**func {
                TypeFunc::Infer => Ok(Monotype::TypeVariable(context.new_typevar())),
                TypeFunc::Enum(name) => match context.get_alias(name).cloned() {
                    None => Ok(Monotype::TypeFuncApplication(func.clone(), expanded_args)),
                    Some(alias) => {
                        if visited.contains(name) {
                            return Err(UnificationError { message: format!("Recursive type alias: {}", name) });
                        }
                        if expanded_args.len() != alias.params.len() {
                            return Err(UnificationError { message: format!("Type alias `{}` expects {} argument(s), got {}", name, alias.params.len(), expanded_args.len()) });
                        }
                        let mut sub : HashMap<String, Monotype> = HashMap::new();
                        for (p, a) in alias.params.iter().zip(expanded_args.iter()) {
                            sub.insert(p.clone(), a.clone());
                        }
                        let instantiated = alias.rhs.instantiate(&mut sub);
                        visited.push(name.clone());
                        let result = expand(&instantiated, context, visited);
                        visited.pop();
                        result
                    }
                },
                _ => Ok(Monotype::TypeFuncApplication(func.clone(), expanded_args)),
            }
        }
    }
}

pub fn type_to_typefn(typ : &Type, context : &mut TypeContext) -> Result<Monotype, UnificationError> {
    expand(&typ.t, context, &mut Vec::new())
}

fn check_undeclared(typ : &Monotype, declared : &[String]) -> Result<(), UnificationError> {
    let undeclared = diff(typ.free_variables(), declared.to_vec());
    if undeclared.is_empty() {
        Ok(())
    } else {
        Err(UnificationError { message: format!("Undeclared type variable(s): {:?}", undeclared) })
    }
}

pub fn handle_type_decl(header : &TypeHeader, dec : &TypeDec, context : &mut TypeContext) -> Result<(), UnificationError> {
    let mut mapping : HashMap<String, Monotype> = HashMap::new();
    let mut fresh_vars : Vec<Monotype> = Vec::new();
    let mut fresh_names : Vec<String> = Vec::new();
    for name in &header.tvars {
        let fresh_name = context.new_typevar();
        let fresh = Monotype::var(fresh_name.clone());
        mapping.insert(name.clone(), fresh.clone());
        fresh_vars.push(fresh);
        fresh_names.push(fresh_name);
    }
    match dec {
        TypeDec::Enum(variants) => {
            if context.get_alias(&header.n).is_some() {
                return Err(UnificationError { message: format!("`{}` is already declared as a type alias", header.n) });
            }
            if context.has_enum_name(&header.n) {
                return Err(UnificationError { message: format!("Enum `{}` is already declared", header.n) });
            }
            context.add_enum_name(header.n.clone());
            let enum_typ = Monotype::enum_app(header.n.clone(), fresh_vars);
            for variant in variants {
                let mut ctor = enum_typ.clone();
                for field in variant.tparams.iter().rev() {
                    let inst = field.t.instantiate(&mut mapping);
                    let expanded = expand(&inst, context, &mut Vec::new())?;
                    ctor = Monotype::func(vec![expanded, ctor]);
                }
                check_undeclared(&ctor, &fresh_names)?;
                context.add(variant.n.clone(), context.generalise(&ctor));
            }
        },
        TypeDec::Alias(rhs) => {
            if context.get_alias(&header.n).is_some() {
                return Err(UnificationError { message: format!("Type alias `{}` is already declared", header.n) });
            }
            if context.has_enum_name(&header.n) {
                return Err(UnificationError { message: format!("`{}` is already declared as an enum", header.n) });
            }
            let elaborated = rhs.t.instantiate(&mut mapping);
            check_undeclared(&elaborated, &fresh_names)?;
            context.add_alias(header.n.clone(), TypeAlias { params : fresh_names, rhs : elaborated });
        },
    }
    Ok(())
}

/*
* Bottom-Up algo
*/
pub fn algo_w(context : &mut TypeContext, expr : &Expr) -> Result<(Substitution, Monotype), UnificationError> {
    match &*expr.e {
        ENode::Variable(name) => match context.get(name) {
            Some(poly) => {
                Ok((Substitution::new(), poly.instantiate(context, None)))
            }
            _ => Err(UnificationError { message: format!("Undefined variable {}!", name) } )
        },
        ENode::Abstraction(bind, exp) => {
            let Binding(name, typp) = &**bind;
            let beta_mon = type_to_typefn(typp, context)?;
            let beta_poly = Polytype::Mono(Box::new(beta_mon.clone()));
            let old_binding = context.get(name);
            context.add(name.clone(), beta_poly);
            let (sub1, t1) = algo_w(context, exp)?;
            match old_binding {
                Some(poly) => context.add(name.clone(), poly),
                None => context.remove(name),
            }
            let beta = Monotype::TypeFuncApplication(Box::new(TypeFunc::Fn), vec!(beta_mon, t1)).apply(&sub1);
            Ok((sub1, beta))
        },
        ENode::Application(exp1, exp2) => {
            let (s1, t1) = algo_w(context, exp1)?;
            *context = context.apply(&s1);
            let (s2, t2) = algo_w(context, exp2)?;
            let ret_var = Monotype::var(context.new_typevar());
            let beta = TypeFuncApplication(Box::new(TypeFunc::Fn), vec!(t2, ret_var.clone()));
            let s3 = unify(&t1.apply(&s2), &beta)?;
            Ok((s1.combine(s2).combine(s3.clone()), ret_var.apply(&s3)))
        },
        ENode::Let(name, exp1, exp2) => {
            let rec_var = Monotype::var(context.new_typevar());
            let old_binding = context.get(name);
            context.add(name.clone(), Polytype::Mono(Box::new(rec_var.clone())));
            let (s1, t1) = algo_w(context, exp1)?;
            *context = context.apply(&s1);
            let s_rec = unify(&t1, &rec_var.apply(&s1))?;
            let combined = s1.combine(s_rec.clone());
            *context = context.apply(&combined);
            match old_binding {
                Some(poly) => context.add(name.clone(), poly),
                None => context.remove(name),
            }
            context.add(name.clone(), context.generalise(&t1.apply(&s_rec)));
            let (s2, t2) = algo_w(context, exp2)?;
            Ok((combined.combine(s2), t2))
        }
        ENode::IfElse(cond, exp1, exp2) => {
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
        ENode::Block(stmts, exp) => {
            let mut combined = Substitution::new();
            for s in stmts {
                match &*s.s {
                    SNode::Decl(e1, t1, e2) => {
                        let var_name = match &*e1.e {
                            ENode::Variable(name) => name.clone(),
                            _ => return Err(UnificationError { message: "Expected a variable name in declaration".to_string() }),
                        };
                        let binding_type = type_to_typefn(t1, context)?;
                        let old_binding = context.get(&var_name);
                        context.add(var_name.clone(), Polytype::Mono(Box::new(binding_type.clone())));
                        let (s1, inferred_type) = algo_w(context, e2)?;
                        *context = context.apply(&s1);
                        combined = combined.combine(s1);
                        let s2 = unify(&binding_type.apply(&combined), &inferred_type)?;
                        *context = context.apply(&s2);
                        combined = combined.combine(s2);
                        match old_binding {
                            Some(poly) => context.add(var_name.clone(), poly),
                            None => context.remove(&var_name),
                        }
                        let resolved = binding_type.apply(&combined);
                        context.add(var_name, context.generalise(&resolved));
                    },
                    SNode::Expr(e1) => {
                        let (s1, _) = algo_w(context, e1)?;
                        *context = context.apply(&s1);
                        combined = combined.combine(s1);
                    },
                    SNode::Print(e1) => {
                        let (s1, t1) = algo_w(context, e1)?;
                        *context = context.apply(&s1);
                        combined = combined.combine(s1);
                        let s2 = unify(&t1, &Monotype::string())?;
                        *context = context.apply(&s2);
                        combined = combined.combine(s2);
                    },
                    SNode::TypeDecl(_, _) => return Err(UnificationError {
                        message: "Type declarations are not allowed inside block expressions".to_string()
                    }),
                }
            }
            let (s_exp, t_exp) = algo_w(context, exp)?;
            combined = combined.combine(s_exp);
            Ok((combined, t_exp))
        },
        ENode::List(exps) => {
            if exps.is_empty() {
                let tv = Monotype::var(context.new_typevar());
                Ok((Substitution::new(), Monotype::list(vec![tv])))
            } else {
                let (s0, t0) = algo_w(context, &exps[0])?;
                *context = context.apply(&s0);
                let mut combined = s0;
                let mut elem_type = t0;
                for e in &exps[1..] {
                    let (s_i, t_i) = algo_w(context, e)?;
                    *context = context.apply(&s_i);
                    combined = combined.combine(s_i);
                    let s_u = unify(&elem_type, &t_i)?;
                    combined = combined.combine(s_u.clone());
                    elem_type = elem_type.apply(&s_u);
                }
                Ok((combined, Monotype::list(vec![elem_type])))
            }
        },
        ENode::Cons(e1, e2) => {
            let (s1, t1) = algo_w(context, e1)?;
            *context = context.apply(&s1);
            let (s2, t2) = algo_w(context, e2)?;
            let elem = t1.apply(&s2);
            let s3 = unify(&t2, &Monotype::list(vec![elem.clone()]))?;
            let result = Monotype::list(vec![elem.apply(&s3)]);
            Ok((s1.combine(s2).combine(s3), result))
        },
        ENode::Arithmetic(op, e1, e2) => {
            let (s1, t1) = algo_w(context, e1)?;
            *context = context.apply(&s1);
            let (s2, t2) = algo_w(context, e2)?;
            let s3 = unify(&t1.apply(&s2), &t2)?;
            let unified = t1.apply(&s2).apply(&s3);
            if !matches!(unified, Monotype::TypeVariable(_)) {
                match op {
                    ArithOp::Plus => {
                        unify(&unified, &Monotype::int())
                            .or_else(|_| unify(&unified, &Monotype::float()))
                            .or_else(|_| unify(&unified, &Monotype::string()))
                            .map_err(|_| UnificationError { message: format!("'+' requires int, float, or string operands, got {:?}", unified) })?;
                    },
                    _ => {
                        unify(&unified, &Monotype::int())
                            .or_else(|_| unify(&unified, &Monotype::float()))
                            .map_err(|_| UnificationError { message: format!("{:?} requires int or float operands, got {:?}", op, unified) })?;
                    },
                }
            }
            Ok((s1.combine(s2).combine(s3), unified))
        },
        ENode::Comparison(op, e1, e2) => {
            let (s1, t1) = algo_w(context, e1)?;
            *context = context.apply(&s1);
            let (s2, t2) = algo_w(context, e2)?;
            let s3 = unify(&t1.apply(&s2), &t2)?;
            let unified = t1.apply(&s2).apply(&s3);
            if !matches!(unified, Monotype::TypeVariable(_)) {
                match op {
                    CompOp::Eq | CompOp::NotEq => {
                        if let Monotype::TypeFuncApplication(f, _) = &unified {
                            if **f == TypeFunc::Fn {
                                return Err(UnificationError { message: "Cannot compare function types".to_string() });
                            }
                        }
                        let op_name = if *op == CompOp::Eq { "==" } else { "!=" };
                        unify(&unified, &Monotype::int())
                            .or_else(|_| unify(&unified, &Monotype::float()))
                            .or_else(|_| unify(&unified, &Monotype::string()))
                            .or_else(|_| unify(&unified, &Monotype::bool()))
                            .map_err(|_| UnificationError { message: format!("'{}' requires int, float, string, or bool operands", op_name) })?;
                    },
                    _ => {
                        unify(&unified, &Monotype::int())
                            .or_else(|_| unify(&unified, &Monotype::float()))
                            .map_err(|_| UnificationError { message: "Comparison requires int or float operands".to_string() })?;
                    },
                }
            }
            Ok((s1.combine(s2).combine(s3), Monotype::bool()))
        },
        ENode::Logical(_, e1, e2) => {
            let (s1, t1) = algo_w(context, e1)?;
            *context = context.apply(&s1);
            let (s2, t2) = algo_w(context, e2)?;
            let s3 = unify(&t1.apply(&s2), &t2)?;
            let unified = t1.apply(&s2).apply(&s3);
            let s4 = unify(&unified, &Monotype::bool())
                .map_err(|_| UnificationError { message: format!("Logical operations require bool operands, got {:?}", unified) })?;
            Ok((s1.combine(s2).combine(s3).combine(s4), Monotype::bool()))
        },
        ENode::Unary(op, e) => match op {
            UnaryOp::Negate => {
                let (s1, t1) = algo_w(context, e)?;
                if matches!(t1, Monotype::TypeVariable(_)) {
                    *context = context.apply(&s1);
                    return Ok((s1, t1));
                }
                let s2 = unify(&t1, &Monotype::int())
                    .or_else(|_| unify(&t1, &Monotype::float()))
                    .map_err(|_| UnificationError { message: format!("Unary negation requires int or float operand, got {:?}", t1) })?;
                let s3 = s1.combine(s2);
                *context = context.apply(&s3);
                Ok((s3.clone(), t1.apply(&s3)))
            },
            UnaryOp::Not => {
                let (s1, t1) = algo_w(context, e)?;
                let s2 = unify(&t1, &Monotype::bool())?;
                let s3 = s1.combine(s2);
                *context = context.apply(&s3);
                Ok((s3.clone(), Monotype::bool()))
            },
        }
        ENode::Literal(lit) => {
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

/*
* Top-Down algo
*/
#[allow(dead_code)]
pub fn algo_m(context : &mut TypeContext, expr : &Expr, typ : &Monotype) -> Result<Substitution, UnificationError> {
    match &*expr.e {
        ENode::Variable(name) => {
            match context.get(name) {
                Some(poly) => {
                    Ok(unify(typ, &poly.instantiate(context, None))?)
                }
                _ => Err(UnificationError { message: format!("Undefined variable {}!", name) } )
            }
        },
        ENode::Abstraction(bind, exp) => {
            let beta1 = Monotype::var(context.new_typevar());
            let beta2 = Monotype::var(context.new_typevar());
            let s1 = unify(typ, &Monotype::func(vec![
                    beta1.clone(), beta2.clone()
                ]))?;

            let Binding(name, typp) = &**bind;
            let beta_mon = type_to_typefn(typp, context)?;
            let s2 = unify(&beta_mon, &beta1.apply(&s1))?;

            let old_binding = context.get(name);
            context.add(name.clone(), Polytype::Mono(Box::new(beta_mon.apply(&s2))));
            let s3 = algo_m(context, exp, &beta2.apply(&s1).apply(&s2))?;
            match old_binding {
                Some(poly) => context.add(name.clone(), poly),
                None => context.remove(name),
            }
            Ok(s1.combine(s2).combine(s3))
        },
        ENode::Application(exp1, exp2) => {
            let beta = Monotype::var(context.new_typevar());
            let s1 = algo_m(context, exp1, &Monotype::func(vec![beta.clone(), typ.clone()]))?;
            let s2 = algo_m(&mut context.apply(&s1), exp2, &beta.apply(&s1))?;
            Ok(s1.combine(s2))
        },
        ENode::Let(name, exp1, exp2) => {
            let rec_var = Monotype::var(context.new_typevar());
            let old_binding = context.get(name);
            context.add(name.clone(), Polytype::Mono(Box::new(rec_var.clone())));
            let beta = Monotype::var(context.new_typevar());
            let s1 = algo_m(context, exp1, &beta)?;
            *context = context.apply(&s1);
            let s_rec = unify(&beta.apply(&s1), &rec_var.apply(&s1))?;
            let combined = s1.combine(s_rec);
            *context = context.apply(&combined);
            match old_binding {
                Some(poly) => context.add(name.clone(), poly),
                None => context.remove(name),
            }
            context.add(name.clone(), context.generalise(&beta.apply(&combined)));
            let s2 = algo_m(context, exp2, &typ.apply(&combined))?;
            Ok(combined.combine(s2))
        },
        ENode::IfElse(cond, exp1, exp2) => {
            let s1 = algo_m(context, cond, &Monotype::bool())?;
            let t1 = typ.apply(&s1);
            let s2 = algo_m(&mut context.apply(&s1), exp1, &t1)?;
            let t2 = t1.apply(&s2);
            let s3 = algo_m(&mut context.apply(&s1).apply(&s2), exp2, &t2)?;
            Ok(s1.combine(s2).combine(s3))
        },
        ENode::Block(stmts, exp) => {
            let mut combined = Substitution::new();
            for s in stmts {
                match &*s.s {
                    SNode::Decl(e1, t1, e2) => {
                        let var_name = match &*e1.e {
                            ENode::Variable(name) => name.clone(),
                            _ => return Err(UnificationError { message: "Expected a variable name in declaration".to_string() }),
                        };
                        let binding_type = type_to_typefn(t1, context)?;
                        let old_binding = context.get(&var_name);
                        context.add(var_name.clone(), Polytype::Mono(Box::new(binding_type.clone())));
                        let beta = Monotype::var(context.new_typevar());
                        let s1 = algo_m(context, e2, &beta)?;
                        *context = context.apply(&s1);
                        combined = combined.combine(s1.clone());
                        let s2 = unify(&binding_type.apply(&combined), &beta.apply(&s1))?;
                        *context = context.apply(&s2);
                        combined = combined.combine(s2);
                        match old_binding {
                            Some(poly) => context.add(var_name.clone(), poly),
                            None => context.remove(&var_name),
                        }
                        let resolved = binding_type.apply(&combined);
                        context.add(var_name, context.generalise(&resolved));
                    },
                    SNode::Expr(e1) => {
                        let beta = Monotype::var(context.new_typevar());
                        let s1 = algo_m(context, e1, &beta)?;
                        *context = context.apply(&s1);
                        combined = combined.combine(s1);
                    },
                    SNode::Print(e1) => {
                        let s1 = algo_m(context, e1, &Monotype::string())?;
                        *context = context.apply(&s1);
                        combined = combined.combine(s1);
                    },
                    SNode::TypeDecl(_, _) => return Err(UnificationError {
                        message: "Type declarations are not allowed inside block expressions".to_string()
                    }),
                }
            }
            let s_final = algo_m(context, exp, &typ.apply(&combined))?;
            combined = combined.combine(s_final);
            Ok(combined)
        },
        ENode::List(exps) => {
            if exps.is_empty() {
                let tv = Monotype::var(context.new_typevar());
                unify(&Monotype::list(vec![tv]), typ)
            } else {
                let beta = Monotype::var(context.new_typevar());
                let s0 = unify(&Monotype::list(vec![beta.clone()]), typ)?;
                *context = context.apply(&s0);
                let mut combined = s0;
                let mut elem_type = beta.apply(&combined);
                for e in exps {
                    let s_i = algo_m(context, e, &elem_type)?;
                    *context = context.apply(&s_i);
                    combined = combined.combine(s_i.clone());
                    elem_type = elem_type.apply(&s_i);
                }
                Ok(combined)
            }
        },
        ENode::Cons(e1, e2) => {
            let beta = Monotype::var(context.new_typevar());
            let s0 = unify(&Monotype::list(vec![beta.clone()]), typ)?;
            *context = context.apply(&s0);
            let elem_type = beta.apply(&s0);
            let s1 = algo_m(context, e1, &elem_type)?;
            *context = context.apply(&s1);
            let s2 = algo_m(context, e2, &Monotype::list(vec![elem_type.apply(&s1)]))?;
            Ok(s0.combine(s1).combine(s2))
        },
        ENode::Arithmetic(op, e1, e2) => {
            let beta = Monotype::var(context.new_typevar());
            let s1 = algo_m(context, e1, &beta)?;
            let s2 = algo_m(&mut context.apply(&s1), e2, &beta.apply(&s1))?;
            let resolved = beta.apply(&s1).apply(&s2);
            let s0 = unify(typ, &resolved)?;
            let resolved = resolved.apply(&s0);
            if !matches!(resolved, Monotype::TypeVariable(_)) {
                match op {
                    ArithOp::Plus => {
                        unify(&resolved, &Monotype::int())
                            .or_else(|_| unify(&resolved, &Monotype::float()))
                            .or_else(|_| unify(&resolved, &Monotype::string()))
                            .map_err(|_| UnificationError { message: format!("'+' requires int, float, or string operands, got {:?}", resolved) })?;
                    },
                    _ => {
                        unify(&resolved, &Monotype::int())
                            .or_else(|_| unify(&resolved, &Monotype::float()))
                            .map_err(|_| UnificationError { message: format!("{:?} requires int or float operands, got {:?}", op, resolved) })?;
                    },
                }
            }
            Ok(s0.combine(s1).combine(s2))
        },
        ENode::Comparison(op, e1, e2) => {
            let s0 = unify(typ, &Monotype::bool())
                .map_err(|_| UnificationError { message: format!("Comparison requires bool result, got {:?}", typ) })?;
            let beta = Monotype::var(context.new_typevar());
            let s1 = algo_m(context, e1, &beta)?;
            let s2 = algo_m(&mut context.apply(&s1), e2, &beta.apply(&s1))?;
            let resolved = beta.apply(&s1).apply(&s2);
            if !matches!(resolved, Monotype::TypeVariable(_)) {
                match op {
                    CompOp::Eq | CompOp::NotEq => {
                        if let Monotype::TypeFuncApplication(f, _) = &resolved {
                            if **f == TypeFunc::Fn {
                                return Err(UnificationError { message: "Cannot compare function types".to_string() });
                            }
                        }
                        let op_name = if *op == CompOp::Eq { "==" } else { "!=" };
                        unify(&resolved, &Monotype::int())
                            .or_else(|_| unify(&resolved, &Monotype::float()))
                            .or_else(|_| unify(&resolved, &Monotype::string()))
                            .or_else(|_| unify(&resolved, &Monotype::bool()))
                            .map_err(|_| UnificationError { message: format!("'{}' requires int, float, string, or bool operands", op_name) })?;
                    },
                    _ => {
                        unify(&resolved, &Monotype::int())
                            .or_else(|_| unify(&resolved, &Monotype::float()))
                            .map_err(|_| UnificationError { message: "Comparison requires int or float operands".to_string() })?;
                    },
                }
            }
            Ok(s0.combine(s1).combine(s2))
        },
        ENode::Logical(_, e1, e2) => {
            let s0 = unify(typ, &Monotype::bool())
                .map_err(|_| UnificationError { message: format!("Logical operations require bool result, got {:?}", typ) })?;
            let s1 = algo_m(context, e1, &Monotype::bool())?;
            let s2 = algo_m(&mut context.apply(&s1), e2, &Monotype::bool())?;
            Ok(s0.combine(s1).combine(s2))
        },
        ENode::Unary(op, e) => match op {
            UnaryOp::Negate => {
                let beta = Monotype::var(context.new_typevar());
                let s0 = algo_m(context, e, &beta)?;
                let resolved = beta.apply(&s0);
                let s0_typ = unify(&resolved, typ)?;
                let resolved = resolved.apply(&s0_typ);
                let s1 = s0.combine(s0_typ);
                if matches!(resolved, Monotype::TypeVariable(_)) {
                    *context = context.apply(&s1);
                    return Ok(s1);
                }
                let s2 = unify(&resolved, &Monotype::int())
                    .or_else(|_| unify(&resolved, &Monotype::float()))
                    .map_err(|_| UnificationError { message: format!("Unary negation requires int or float operand, got {:?}", resolved) })?;
                let s3 = s1.combine(s2);
                *context = context.apply(&s3);
                Ok(s3.clone())
            },
            UnaryOp::Not => {
                let s0 = unify(typ, &Monotype::bool())
                    .map_err(|_| UnificationError { message: format!("Unary not requires bool result, got {:?}", typ)})?;
                let beta = Monotype::var(context.new_typevar());
                let s1 = algo_m(context, e, &beta)?;
                let s2 = unify(&beta.apply(&s1), &Monotype::bool())?;
                Ok(s0.combine(s1).combine(s2))
            },
        },
        ENode::Literal(lit) => {
            let t = match lit.as_ref() {
                Lit::Int(_) => Monotype::int(),
                Lit::Bool(_) => Monotype::bool(),
                Lit::Str(_) => Monotype::string(),
                Lit::Float(_) => Monotype::float(),
                Lit::Unit => Monotype::unit(),
            };
            unify(typ, &t)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ENode;

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
        assert_eq!(result.variables.get("c"), Some(&int()));
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
        let map = mappings(vec![]);
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

// Block expression    #[test]
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

    // ---- Expr tree helpers ---- //

    fn v(name: &str) -> Box<Expr> {
        Box::new(Expr::from(ENode::Variable(name.to_string())))
    }

    fn lit(l: Lit) -> Box<Expr> {
        Box::new(Expr::from(ENode::Literal(Box::new(l))))
    }

    fn lam_infer(name: &str, body: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::Abstraction(
            Box::new(Binding(name.to_string(), Box::new(Type { t: Monotype::infer() }))),
            body,
        )))
    }

    fn lam_annot(name: &str, annot: Monotype, body: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::Abstraction(
            Box::new(Binding(name.to_string(), Box::new(Type { t: annot }))),
            body,
        )))
    }

    fn app(e1: Box<Expr>, e2: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::Application(e1, e2)))
    }

    fn let_in(name: &str, e1: Box<Expr>, e2: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::Let(name.to_string(), e1, e2)))
    }

    fn if_else(cond: Box<Expr>, e1: Box<Expr>, e2: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::IfElse(cond, e1, e2)))
    }

    fn list(exps: Vec<Box<Expr>>) -> Box<Expr> {
        Box::new(Expr::from(ENode::List(exps.into_iter().map(|b| *b).collect())))
    }

    fn cons(e1: Box<Expr>, e2: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::Cons(e1, e2)))
    }

    fn unary(op: UnaryOp, e: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::from(ENode::Unary(op, e)))
    }

    fn ctx_with(pairs: Vec<(&str, Polytype)>) -> TypeContext {
        TypeContext::make(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    // ===== algo_w tests =====

    #[test]
    fn w_literal_int() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lit(Lit::Int(42)));
        assert_eq!(result, Ok((Substitution::new(), int())));
    }

    #[test]
    fn w_literal_bool() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lit(Lit::Bool(true)));
        assert_eq!(result, Ok((Substitution::new(), bool())));
    }

    #[test]
    fn w_literal_str() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lit(Lit::Str("hi".to_string())));
        assert_eq!(result, Ok((Substitution::new(), Monotype::string())));
    }

    #[test]
    fn w_literal_float() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lit(Lit::Float(1.5)));
        assert_eq!(result, Ok((Substitution::new(), Monotype::float())));
    }

    #[test]
    fn w_literal_unit() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lit(Lit::Unit));
        assert_eq!(result, Ok((Substitution::new(), Monotype::unit())));
    }

    #[test]
    fn w_var_in_context() {
        let mut ctx = ctx_with(vec![("x", mono(int()))]);
        let result = algo_w(&mut ctx, &v("x"));
        assert_eq!(result, Ok((Substitution::new(), int())));
    }

    #[test]
    fn w_var_poly() {
        let mut ctx = ctx_with(vec![("id", forall("a", mono(fn_type(var("a"), var("a")))))]);
        let result = algo_w(&mut ctx, &v("id"));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, fn_type(var("t0"), var("t0")));
    }

    #[test]
    fn w_var_undefined() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &v("x"));
        assert!(result.is_err());
    }

    // ---- W: list expressions ----

    #[test]
    fn w_list_empty() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &list(vec![]));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert!(matches!(typ, Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::List));
    }

    #[test]
    fn w_list_int() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &list(vec![lit(Lit::Int(1)), lit(Lit::Int(2))]));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![Monotype::int()]));
    }

    #[test]
    fn w_list_bool() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &list(vec![lit(Lit::Bool(true)), lit(Lit::Bool(false))]));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![Monotype::bool()]));
    }

    #[test]
    fn w_list_mixed_type_error() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &list(vec![lit(Lit::Int(1)), lit(Lit::Bool(true))]));
        assert!(result.is_err());
    }

    #[test]
    fn w_list_single() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &list(vec![lit(Lit::Float(3.14))]));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![Monotype::float()]));
    }

    #[test]
    fn w_cons_int_nil() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &cons(lit(Lit::Int(1)), list(vec![])));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![Monotype::int()]));
    }

    #[test]
    fn w_cons_nested() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &cons(lit(Lit::Int(1)), cons(lit(Lit::Int(2)), list(vec![]))));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![Monotype::int()]));
    }

    #[test]
    fn w_cons_head_type_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &cons(lit(Lit::Int(1)), cons(lit(Lit::Bool(true)), list(vec![]))));
        assert!(result.is_err());
    }

    #[test]
    fn w_cons_tail_not_list() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &cons(lit(Lit::Int(1)), lit(Lit::Int(2))));
        assert!(result.is_err());
    }

    #[test]
    fn w_cons_polymorphic() {
        let mut ctx = TypeContext::new();
        ctx.add("x".to_string(), Polytype::Mono(Box::new(var("a"))));
        let result = algo_w(&mut ctx, &cons(v("x"), list(vec![])));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![var("a")]));
    }

    #[test]
    fn w_list_with_variable() {
        let mut ctx = TypeContext::new();
        ctx.add("x".to_string(), Polytype::Mono(Box::new(Monotype::int())));
        let result = algo_w(&mut ctx, &list(vec![v("x"), v("x")]));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, Monotype::list(vec![Monotype::int()]));
    }

    #[test]
    fn w_abstraction_identity() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lam_infer("x", v("x")));
        assert!(result.is_ok());
        let (sub, typ) = result.unwrap();
        assert_eq!(sub, Substitution::new());
        assert_eq!(typ, fn_type(var("t0"), var("t0")));
    }

    #[test]
    fn w_abstraction_annotated() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &lam_annot("x", int(), v("x")));
        assert_eq!(result, Ok((Substitution::new(), fn_type(int(), int()))));
    }

    #[test]
    fn w_abstraction_closure() {
        let mut ctx = ctx_with(vec![("y", mono(bool()))]);
        let result = algo_w(&mut ctx, &lam_infer("x", v("y")));
        assert!(result.is_ok());
        let (sub, typ) = result.unwrap();
        assert_eq!(sub, Substitution::new());
        assert_eq!(typ, fn_type(var("t0"), bool()));
    }

    #[test]
    fn w_application_id_to_int() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &app(lam_infer("x", v("x")), lit(Lit::Int(5))));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, int());
    }

    #[test]
    fn w_let_simple() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &let_in("x", lit(Lit::Int(5)), v("x")));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, int());
    }

    #[test]
    fn w_let_polymorphic_id() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &let_in("id", lam_infer("x", v("x")), app(v("id"), lit(Lit::Int(5)))));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, int());
    }

    #[test]
    fn w_if_else_int() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Int(2))));
        assert!(result.is_ok());
        let (_sub, typ) = result.unwrap();
        assert_eq!(typ, int());
    }

    #[test]
    fn w_if_else_cond_not_bool() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &if_else(lit(Lit::Int(1)), lit(Lit::Int(2)), lit(Lit::Int(3))));
        assert!(result.is_err());
    }

    #[test]
    fn w_if_else_branches_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Bool(false))));
        assert!(result.is_err());
    }

    // ===== W: unary expressions =====

    #[test]
    fn w_negate_int() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Int(5))));
        assert_eq!(result, Ok((Substitution::new(), int())));
    }

    #[test]
    fn w_negate_float() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Float(3.14))));
        assert_eq!(result, Ok((Substitution::new(), Monotype::float())));
    }

    #[test]
    fn w_negate_string_error() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Str("hi".to_string()))));
        assert!(result.is_err());
    }

    #[test]
    fn w_not_bool() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Bool(true))));
        assert_eq!(result, Ok((Substitution::new(), bool())));
    }

    #[test]
    fn w_not_int_error() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Int(5))));
        assert!(result.is_err());
    }

    #[test]
    fn w_not_string_error() {
        let mut ctx = TypeContext::new();
        let result = algo_w(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Str("hi".to_string()))));
        assert!(result.is_err());
    }

    // ===== M: unary expressions =====

    #[test]
    fn m_negate_int_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Int(5))), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_negate_int_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Int(5))), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_negate_float_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Float(1.5))), &Monotype::float());
        assert!(result.is_ok());
    }

    #[test]
    fn m_negate_refines_var() {
        let mut ctx = TypeContext::new();
        let tv = var("a");
        let result = algo_m(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Int(5))), &tv);
        assert!(result.is_ok());
        let sub = result.unwrap();
        assert_eq!(tv.apply(&sub), int());
    }

    #[test]
    fn m_negate_string_via_typ_error() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Negate, lit(Lit::Int(5))), &Monotype::string());
        assert!(result.is_err());
    }

    #[test]
    fn m_not_bool_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Bool(true))), &bool());
        assert!(result.is_ok());
    }

    #[test]
    fn m_not_bool_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Bool(true))), &int());
        assert!(result.is_err());
    }

    #[test]
    fn m_not_refines_var() {
        let mut ctx = TypeContext::new();
        let tv = var("a");
        let result = algo_m(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Bool(true))), &tv);
        assert!(result.is_ok());
        let sub = result.unwrap();
        assert_eq!(tv.apply(&sub), bool());
    }

    #[test]
    fn m_not_int_operand_error() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Int(5))), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_not_string_operand_error() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &unary(UnaryOp::Not, lit(Lit::Str("hi".to_string()))), &bool());
        assert!(result.is_err());
    }

    // ===== algo_m tests =====

    #[test]
    fn m_literal_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lit(Lit::Int(42)), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_literal_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lit(Lit::Int(42)), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_literal_refines_var() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lit(Lit::Int(42)), &var("a"));
        assert_eq!(result, ok(vec![("a", int())]));
    }

    // ---- M: list expressions ----

    #[test]
    fn m_list_empty_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &list(vec![]), &Monotype::list(vec![Monotype::int()]));
        assert!(result.is_ok());
    }

    #[test]
    fn m_list_empty_refines_var() {
        let mut ctx = TypeContext::new();
        let tv = Monotype::var("a".to_string());
        let result = algo_m(&mut ctx, &list(vec![]), &tv);
        assert!(result.is_ok());
        let sub = result.unwrap();
        let resolved = tv.apply(&sub);
        assert!(matches!(resolved, Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::List));
    }

    #[test]
    fn m_list_int_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(
            &mut ctx,
            &list(vec![lit(Lit::Int(1)), lit(Lit::Int(2))]),
            &Monotype::list(vec![Monotype::int()]),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn m_list_int_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(
            &mut ctx,
            &list(vec![lit(Lit::Int(1)), lit(Lit::Bool(true))]),
            &Monotype::list(vec![Monotype::int()]),
        );
        assert!(result.is_err());
    }

    #[test]
    fn m_list_wrong_outer_type() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &list(vec![]), &Monotype::int());
        assert!(result.is_err());
    }

    #[test]
    fn m_list_bool_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(
            &mut ctx,
            &list(vec![lit(Lit::Bool(true)), lit(Lit::Bool(false))]),
            &Monotype::list(vec![Monotype::bool()]),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn m_list_refines_elem_var() {
        let mut ctx = TypeContext::new();
        let tv = Monotype::var("a".to_string());
        let list_tv = Monotype::list(vec![tv.clone()]);
        let result = algo_m(&mut ctx, &list(vec![lit(Lit::Int(42))]), &list_tv);
        assert!(result.is_ok());
        let sub = result.unwrap();
        assert_eq!(tv.apply(&sub), Monotype::int());
    }

    #[test]
    fn m_cons_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &cons(lit(Lit::Int(1)), list(vec![])), &Monotype::list(vec![Monotype::int()]));
        assert!(result.is_ok());
    }

    #[test]
    fn m_cons_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &cons(lit(Lit::Int(1)), list(vec![])), &Monotype::list(vec![Monotype::bool()]));
        assert!(result.is_err());
    }

    #[test]
    fn m_cons_refines_elem_var() {
        let mut ctx = TypeContext::new();
        let tv = Monotype::var("a".to_string());
        let list_tv = Monotype::list(vec![tv.clone()]);
        let result = algo_m(&mut ctx, &cons(lit(Lit::Int(42)), list(vec![])), &list_tv);
        assert!(result.is_ok());
        let sub = result.unwrap();
        assert_eq!(tv.apply(&sub), Monotype::int());
    }

    #[test]
    fn m_cons_wrong_outer_type() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &cons(lit(Lit::Int(1)), list(vec![])), &Monotype::int());
        assert!(result.is_err());
    }

    #[test]
    fn m_list_empty_wrong_outer_type() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &list(vec![]), &Monotype::bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_var_matches() {
        let mut ctx = ctx_with(vec![("x", mono(int()))]);
        let result = algo_m(&mut ctx, &v("x"), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_var_mismatch() {
        let mut ctx = ctx_with(vec![("x", mono(int()))]);
        let result = algo_m(&mut ctx, &v("x"), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_var_undefined() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &v("x"), &int());
        assert!(result.is_err());
    }

    #[test]
    fn m_abstraction_matches_fn() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lam_infer("x", v("x")), &fn_type(int(), int()));
        assert!(result.is_ok());
    }

    #[test]
    fn m_abstraction_with_annot_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lam_annot("x", int(), v("x")), &fn_type(int(), int()));
        assert!(result.is_ok());
    }

    #[test]
    fn m_abstraction_annot_mismatches_expected() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lam_annot("x", bool(), v("x")), &fn_type(int(), int()));
        assert!(result.is_err());
    }

    #[test]
    fn m_abstraction_expected_not_fn() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lam_infer("x", v("x")), &int());
        assert!(result.is_err());
    }

    #[test]
    fn m_abstraction_return_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &lam_infer("x", lit(Lit::Int(5))), &fn_type(int(), bool()));
        assert!(result.is_err());
    }

    #[test]
    fn m_application_id_to_int() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &app(lam_infer("x", v("x")), lit(Lit::Int(5))), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_application_wrong_result_type() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &app(lam_infer("x", v("x")), lit(Lit::Int(5))), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_let_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &let_in("x", lit(Lit::Int(5)), v("x")), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_let_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &let_in("x", lit(Lit::Int(5)), v("x")), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_let_polymorphic_id() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &let_in("id", lam_infer("x", v("x")), app(v("id"), lit(Lit::Int(5)))), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_if_else_matches() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Int(2))), &int());
        assert!(result.is_ok());
    }

    #[test]
    fn m_if_else_wrong_type() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Int(2))), &bool());
        assert!(result.is_err());
    }

    #[test]
    fn m_if_else_cond_not_bool() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &if_else(lit(Lit::Int(1)), lit(Lit::Int(2)), lit(Lit::Int(3))), &int());
        assert!(result.is_err());
    }

    #[test]
    fn m_if_else_branches_mismatch() {
        let mut ctx = TypeContext::new();
        let result = algo_m(&mut ctx, &if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Bool(false))), &int());
        assert!(result.is_err());
    }

    // ===== algo_w / algo_m agreement tests =====

    #[test]
    fn w_and_m_agree_literal_int() {
        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &lit(Lit::Int(42))).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &lit(Lit::Int(42)), &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_abstraction_identity() {
        let expr = lam_infer("x", v("x"));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_annotated_abstraction() {
        let expr = lam_annot("x", int(), v("x"));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_application() {
        let expr = app(lam_infer("x", v("x")), lit(Lit::Int(5)));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_let() {
        let expr = let_in("x", lit(Lit::Int(5)), v("x"));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_if_else() {
        let expr = if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Int(2)));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_mismatch_rejected() {
        let expr = lit(Lit::Int(42));

        let mut ctx_w = TypeContext::new();
        let (_sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        // typ_w is Int; pass Bool to algo_m — should fail
        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &bool());
        assert!(result_m.is_err());
    }

    #[test]
    fn w_and_m_agree_polymorphic_let() {
        let expr = let_in("id", lam_infer("x", v("x")), app(v("id"), lit(Lit::Int(5))));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_negate_int() {
        let expr = unary(UnaryOp::Negate, lit(Lit::Int(42)));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }

    #[test]
    fn w_and_m_agree_not_bool() {
        let expr = unary(UnaryOp::Not, lit(Lit::Bool(true)));

        let mut ctx_w = TypeContext::new();
        let (sub_w, typ_w) = algo_w(&mut ctx_w, &expr).unwrap();
        let resolved = typ_w.apply(&sub_w);

        let mut ctx_m = TypeContext::new();
        let result_m = algo_m(&mut ctx_m, &expr, &resolved);
        assert!(result_m.is_ok());
    }
}
