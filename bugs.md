# Bugs to investigate:

## lambdas as application arguments? (FIXED)

```
❯ cargo run src/prelude/prelude.spcy --repl
warning: unused import: `crate::prelude`
 --> src/ast.rs:3:5
  |
3 | use crate::prelude;
  |     ^^^^^^^^^^^^^^
  |
  = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused import: `ExecutionResult`
  --> src/codegen/mod.rs:25:19
   |
25 | pub use execute::{ExecutionResult, compile, execute};
   |                   ^^^^^^^^^^^^^^^

warning: unused variable: `scrutinee`
    --> src/types.rs:1048:22
     |
1048 |         ENode::Match(scrutinee, cases) => {
     |                      ^^^^^^^^^ help: if this is intentional, prefix it with an underscore: `_scrutinee`
     |
     = note: `#[warn(unused_variables)]` (part of `#[warn(unused)]`) on by default

warning: unused variable: `cases`
    --> src/types.rs:1048:33
     |
1048 |         ENode::Match(scrutinee, cases) => {
     |                                 ^^^^^ help: if this is intentional, prefix it with an underscore: `_cases`

warning: `spicylang2` (bin "spicylang2") generated 4 warnings (run `cargo fix --bin "spicylang2" -p spicylang2` to apply 4 suggestions)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.06s
     Running `target/debug/spicylang2 src/prelude/prelude.spcy --repl`
parse: ok
typecheck: ok
codegen: ok (1 top-level functions)
> lfold (\acc x => x::acc) [] [1,2,3];
error: 'func.call' op operand type mismatch: expected operand type '(!llvm.ptr, i32) -> !llvm.ptr', but provided '(!llvm.ptr) -> !llvm.ptr' for operand number 0
execution error: codegen: pass manager failed: failed to run pass
> 
```

Other example:
```
> let add = \x y => x + y;
  : t84 -> t84 -> t84 : <fn>
> let sym = lfold add 0 [1,2,3,4,5]
  : int = 15
> lfold (\x y => x + y) 0 [1,2,3,4,5]
error: 'func.call' op operand type mismatch: expected operand type '(i32, i32) -> i32', but provided '(i32) -> !llvm.ptr' for operand number 0
execution error: codegen: pass manager failed: failed to run pass
> 
```

## Enum ctors not working

Actually works fine in compiled code, interesting

```
parse: ok
typecheck: ok
codegen: ok (1 top-level functions)
> opt 1;
execution error: codegen: cannot JIT-execute type TypeFuncApplication(Enum("Option"), [TypeFuncApplication(Int, [])])
>  
> get_i 0 [1,2,3]
execution error: codegen: cannot JIT-execute type TypeFuncApplication(Enum("Option"), [TypeFuncApplication(Int, [])])
>   
> let get_res = \opt => match opt | Some val => Ok val | None => Err "no value";
  : Option t198 -> Result t198 str : <fn>
> get_res (Some 0);
execution error: codegen: cannot JIT-execute type TypeFuncApplication(Enum("Result"), [TypeFuncApplication(Int, []), TypeFuncApplication(Str, [])])
> get_res None; 
execution error: codegen: cannot JIT-execute type TypeFuncApplication(Enum("Result"), [TypeVariable("t206"), TypeFuncApplication(Str, [])])
> 
> 
```

## Partial application not supported (FIXED)

```
> let add = \x y => x+1;
  : int -> t2 -> int : <fn>
> add 1;
codegen error: codegen: partial application of `add` is not supported yet
>  
```
