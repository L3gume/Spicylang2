//! Rendering of types for human-readable output.

use crate::types::{Monotype, TypeFunc};

pub fn render_type(t: &Monotype) -> String {
    match t {
        Monotype::TypeVariable(v) => v.clone(),
        Monotype::TypeFuncApplication(f, args) => match **f {
            TypeFunc::Infer => "_".to_string(),
            TypeFunc::Unit => "()".to_string(),
            TypeFunc::Int => "int".to_string(),
            TypeFunc::Float => "float".to_string(),
            TypeFunc::Bool => "bool".to_string(),
            TypeFunc::Str => "str".to_string(),
            TypeFunc::Fn => args.iter().map(render_type).collect::<Vec<_>>().join(" -> "),
            TypeFunc::List => match args.first() {
                Some(elem) => format!("[{}]", render_type(elem)),
                None => "list".to_string(),
            },
            TypeFunc::Enum(ref name) => {
                if args.is_empty() {
                    name.clone()
                } else {
                    let rendered: Vec<String> = args.iter().map(render_type).collect();
                    format!("{} {}", name, rendered.join(" "))
                }
            }
        },
    }
}
