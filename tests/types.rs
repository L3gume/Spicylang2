use merlin_lang::types::*;
use merlin_lang::ast::*;
use std::collections::HashMap;

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
    let mut ctx = TypeContext::make(ctx_map(vec![("x", mono(int()))]));
    assert_eq!(ctx.generalise(&int()), mono(int()));
}

#[test]
fn generalise_single_var_not_in_context() {
    let mut ctx = TypeContext::new();
    assert_eq!(ctx.generalise(&var("a")), forall("t0", mono(var("t0"))));
}

#[test]
fn generalise_single_var_in_context() {
    let mut ctx = TypeContext::make(ctx_map(vec![("x", mono(fn_type(var("a"), int())))]));
    assert_eq!(ctx.generalise(&var("a")), mono(var("a")));
}

#[test]
fn generalise_fn_some_vars_in_context() {
    let mut ctx = TypeContext::make(ctx_map(vec![("x", mono(fn_type(var("a"), int())))]));
    assert_eq!(
        ctx.generalise(&fn_type(var("a"), var("b"))),
        forall("t0", mono(fn_type(var("a"), var("t0"))))
    );
}

#[test]
fn generalise_fn_no_vars_in_context() {
    let mut ctx = TypeContext::new();
    assert_eq!(
        ctx.generalise(&fn_type(var("a"), var("b"))),
        forall("t1", forall("t0", mono(fn_type(var("t0"), var("t1")))))
    );
}

#[test]
fn generalise_fn_all_vars_in_context() {
    let mut ctx = TypeContext::make(ctx_map(vec![
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

fn unify_types(t1: &Monotype, t2: &Monotype) -> Result<Substitution, UnificationError> {
    let mut ctx = TypeContext::new();
    unify(&mut ctx, t1, t2)
}

#[test]
fn unify_same_var() {
    assert_eq!(unify_types(&var("a"), &var("a")), ok(vec![]));
}

#[test]
fn unify_diff_vars() {
    assert_eq!(unify_types(&var("a"), &var("b")), ok(vec![("a", var("b"))]));
}

#[test]
fn unify_var_and_concrete() {
    assert_eq!(unify_types(&var("a"), &int()), ok(vec![("a", int())]));
}

#[test]
fn unify_concrete_and_var() {
    assert_eq!(unify_types(&int(), &var("a")), ok(vec![("a", int())]));
}

#[test]
fn unify_same_concrete() {
    assert_eq!(unify_types(&int(), &int()), ok(vec![]));
}

#[test]
fn unify_different_concretes() {
    let result = unify_types(&int(), &bool());
    assert!(result.is_err());
}

#[test]
fn unify_infinite_type() {
    let result = unify_types(&var("a"), &fn_type(var("a"), int()));
    assert!(result.is_err());
}

#[test]
fn unify_fn_same_structure() {
    assert_eq!(
        unify_types(&fn_type(var("a"), int()), &fn_type(var("b"), int())),
        ok(vec![("a", var("b"))])
    );
}

#[test]
fn unify_fn_chain_substitution() {
    assert_eq!(
        unify_types(&fn_type(var("a"), int()), &fn_type(int(), var("b"))),
        ok(vec![("a", int()), ("b", int())])
    );
}

#[test]
fn unify_fn_different_constructors() {
    let result = unify_types(&fn_type(int(), int()), &fn_type(int(), bool()));
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
    let result = algo_w(&mut ctx, &mut lit(Lit::Int(42)));
    assert_eq!(result, Ok((Substitution::new(), int())));
}

#[test]
fn w_literal_bool() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lit(Lit::Bool(true)));
    assert_eq!(result, Ok((Substitution::new(), bool())));
}

#[test]
fn w_literal_str() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lit(Lit::Str("hi".to_string())));
    assert_eq!(result, Ok((Substitution::new(), Monotype::string())));
}

#[test]
fn w_literal_float() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lit(Lit::Float(1.5)));
    assert_eq!(result, Ok((Substitution::new(), Monotype::float())));
}

#[test]
fn w_literal_unit() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lit(Lit::Unit));
    assert_eq!(result, Ok((Substitution::new(), Monotype::unit())));
}

#[test]
fn w_var_in_context() {
    let mut ctx = ctx_with(vec![("x", mono(int()))]);
    let result = algo_w(&mut ctx, &mut v("x"));
    assert_eq!(result, Ok((Substitution::new(), int())));
}

#[test]
fn w_var_poly() {
    let mut ctx = ctx_with(vec![("id", forall("a", mono(fn_type(var("a"), var("a")))))]);
    let result = algo_w(&mut ctx, &mut v("id"));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, fn_type(var("t0"), var("t0")));
}

#[test]
fn w_var_undefined() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut v("x"));
    assert!(result.is_err());
}

// ---- W: list expressions ----

#[test]
fn w_list_empty() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut list(vec![]));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert!(matches!(typ, Monotype::TypeFuncApplication(f, _) if *f == TypeFunc::List));
}

#[test]
fn w_list_int() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut list(vec![lit(Lit::Int(1)), lit(Lit::Int(2))]));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(Monotype::int()));
}

#[test]
fn w_list_bool() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut list(vec![lit(Lit::Bool(true)), lit(Lit::Bool(false))]));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(Monotype::bool()));
}

#[test]
fn w_list_mixed_type_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut list(vec![lit(Lit::Int(1)), lit(Lit::Bool(true))]));
    assert!(result.is_err());
}

#[test]
fn w_list_single() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut list(vec![lit(Lit::Float(3.14))]));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(Monotype::float()));
}

#[test]
fn w_cons_int_nil() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut cons(lit(Lit::Int(1)), list(vec![])));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(Monotype::int()));
}

#[test]
fn w_cons_nested() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut cons(lit(Lit::Int(1)), cons(lit(Lit::Int(2)), list(vec![]))));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(Monotype::int()));
}

#[test]
fn w_cons_head_type_mismatch() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut cons(lit(Lit::Int(1)), cons(lit(Lit::Bool(true)), list(vec![]))));
    assert!(result.is_err());
}

#[test]
fn w_cons_tail_not_list() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut cons(lit(Lit::Int(1)), lit(Lit::Int(2))));
    assert!(result.is_err());
}

#[test]
fn w_cons_polymorphic() {
    let mut ctx = TypeContext::new();
    ctx.add("x".to_string(), Polytype::Mono(Box::new(var("a"))));
    let result = algo_w(&mut ctx, &mut cons(v("x"), list(vec![])));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(var("a")));
}

#[test]
fn w_list_with_variable() {
    let mut ctx = TypeContext::new();
    ctx.add("x".to_string(), Polytype::Mono(Box::new(Monotype::int())));
    let result = algo_w(&mut ctx, &mut list(vec![v("x"), v("x")]));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, Monotype::list(Monotype::int()));
}

#[test]
fn w_abstraction_identity() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lam_infer("x", v("x")));
    assert!(result.is_ok());
    let (sub, typ) = result.unwrap();
    assert_eq!(sub, Substitution::new());
    assert_eq!(typ, fn_type(var("t0"), var("t0")));
}

#[test]
fn w_abstraction_annotated() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lam_annot("x", int(), v("x")));
    assert_eq!(result, Ok((Substitution::new(), fn_type(int(), int()))));
}

#[test]
fn w_abstraction_closure() {
    let mut ctx = ctx_with(vec![("y", mono(bool()))]);
    let result = algo_w(&mut ctx, &mut lam_infer("x", v("y")));
    assert!(result.is_ok());
    let (sub, typ) = result.unwrap();
    assert_eq!(sub, Substitution::new());
    assert_eq!(typ, fn_type(var("t0"), bool()));
}

#[test]
fn w_application_id_to_int() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut app(lam_infer("x", v("x")), lit(Lit::Int(5))));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, int());
}

#[test]
fn w_let_simple() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut let_in("x", lit(Lit::Int(5)), v("x")));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, int());
}

#[test]
fn w_let_polymorphic_id() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut let_in("id", lam_infer("x", v("x")), app(v("id"), lit(Lit::Int(5)))));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, int());
}

#[test]
fn w_if_else_int() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Int(2))));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, int());
}

#[test]
fn w_if_else_cond_not_bool() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut if_else(lit(Lit::Int(1)), lit(Lit::Int(2)), lit(Lit::Int(3))));
    assert!(result.is_err());
}

#[test]
fn w_if_else_branches_mismatch() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut if_else(lit(Lit::Bool(true)), lit(Lit::Int(1)), lit(Lit::Bool(false))));
    assert!(result.is_err());
}

// ===== W: unary expressions =====

#[test]
fn w_negate_int() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut unary(UnaryOp::Negate, lit(Lit::Int(5))));
    assert_eq!(result, Ok((Substitution::new(), int())));
}

#[test]
fn w_negate_float() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut unary(UnaryOp::Negate, lit(Lit::Float(3.14))));
    assert_eq!(result, Ok((Substitution::new(), Monotype::float())));
}

#[test]
fn w_negate_string_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut unary(UnaryOp::Negate, lit(Lit::Str("hi".to_string()))));
    assert!(result.is_err());
}

#[test]
fn w_not_bool() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut unary(UnaryOp::Not, lit(Lit::Bool(true))));
    assert_eq!(result, Ok((Substitution::new(), bool())));
}

#[test]
fn w_not_int_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut unary(UnaryOp::Not, lit(Lit::Int(5))));
    assert!(result.is_err());
}

#[test]
fn w_not_string_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut unary(UnaryOp::Not, lit(Lit::Str("hi".to_string()))));
    assert!(result.is_err());
}

// ---- Record/row helpers ---- //

fn field_access(e: Box<Expr>, field: &str) -> Box<Expr> {
    Box::new(Expr::from(ENode::FieldAccess(e, field.to_string())))
}

fn record_lit(fields: Vec<(&str, Box<Expr>)>) -> Box<Expr> {
    Box::new(Expr::from(ENode::Record(
        None,
        fields.into_iter().map(|(n, e)| FieldAssn { field: n.to_string(), exp: e }).collect(),
    )))
}

fn with_expr(e: Box<Expr>, fields: Vec<(&str, Box<Expr>)>) -> Box<Expr> {
    Box::new(Expr::from(ENode::With(
        e,
        fields.into_iter().map(|(n, e)| FieldAssn { field: n.to_string(), exp: e }).collect(),
    )))
}

fn rec(inner: Monotype) -> Monotype {
    Monotype::rec(inner)
}

fn row_ext(label: &str, field: Monotype, rest: Monotype) -> Monotype {
    Monotype::row_ext(label.to_string(), field, rest)
}

fn empty_row() -> Monotype {
    Monotype::empty_row()
}

// ===== W: records =====

#[test]
fn w_record_literal() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut record_lit(vec![
        ("bar", lit(Lit::Int(1))),
        ("baz", lit(Lit::Bool(true))),
    ]));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, rec(row_ext("baz", bool(), row_ext("bar", int(), empty_row()))));
}

#[test]
fn w_field_access_concrete() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut field_access(
        record_lit(vec![("bar", lit(Lit::Int(1)))]),
        "bar",
    ));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, int());
}

#[test]
fn w_field_access_on_variable() {
    // `\x => x.name` is typable without a nominal record: the lambda's
    // parameter is constrained to `{ name: α | ρ }` and the result is `α`.
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut lam_infer("x", field_access(v("x"), "name")));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    match typ {
        Monotype::TypeFuncApplication(f, args) => {
            assert_eq!(*f, TypeFunc::Fn);
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Monotype::TypeFuncApplication(g, _) if **g == TypeFunc::Rec));
            assert!(matches!(&args[1], Monotype::TypeVariable(_)));
        }
        other => panic!("expected a function type, got {:?}", other),
    }
}

#[test]
fn w_field_access_missing_field_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut field_access(
        record_lit(vec![("bar", lit(Lit::Int(1)))]),
        "baz",
    ));
    assert!(result.is_err());
}

#[test]
fn w_field_access_on_int_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut field_access(lit(Lit::Int(1)), "bar"));
    assert!(result.is_err());
}

#[test]
fn w_with_update() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut with_expr(
        record_lit(vec![("bar", lit(Lit::Int(1))), ("baz", lit(Lit::Bool(true)))]),
        vec![("bar", lit(Lit::Int(2)))],
    ));
    assert!(result.is_ok());
    let (_sub, typ) = result.unwrap();
    assert_eq!(typ, rec(row_ext("baz", bool(), row_ext("bar", int(), empty_row()))));
}

#[test]
fn w_with_on_int_error() {
    let mut ctx = TypeContext::new();
    let result = algo_w(&mut ctx, &mut with_expr(lit(Lit::Int(1)), vec![("bar", lit(Lit::Int(2)))]));
    assert!(result.is_err());
}

