use merlin_lang::display::render_type;
use merlin_lang::types::Monotype;

fn var(name: &str) -> Monotype {
    Monotype::var(name.to_string())
}

#[test]
fn reuses_mapping_within_one_render() {
    // The same type variable must render with the same name both times.
    let t = Monotype::func(vec![var("t0"), var("t0")]);
    assert_eq!(render_type(&t), "'a -> 'a");
}

#[test]
fn distinct_variables_get_distinct_names() {
    let t = Monotype::func(vec![var("t0"), var("t1")]);
    assert_eq!(render_type(&t), "'a -> 'b");
}

#[test]
fn fresh_mapping_per_call() {
    // The mapping resets on each top-level call.
    let t = Monotype::func(vec![var("t0"), var("t1")]);
    assert_eq!(render_type(&t), "'a -> 'b");
    assert_eq!(render_type(&t), "'a -> 'b");
}
