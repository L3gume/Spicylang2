# TODO List

- [x] Add simple binary expressions to language with strict exact type matching
    - [x] arithmetic expressions (Int, Float, String (Append))
    - [x] comparison expressions (Int, Float), String & Bool equal only
    - [x] logical expressions (Bool only)
    - [ ] (Very Long term) explicit impl of operators for custom types
- [x] Recursive functions
- [x] Fix conflict between negative integer literal and binary - operation
- [ ] MLIR code generation
- [ ] Builtin List stuff (len, head, tail, first, last, whatever else, etc.)
    - [x] builtin cons and list expressions
- [ ] Better parser + lexer
    - [ ] Location info in AST
    - [ ] Better error messages in parse and typecheck
    - [ ] Support comments
- [ ] Pretty-printing of type and AST nodes
- [x] User-defined enumeration types
- [ ] User-defined structure types
- [x] Pattern Matching on expressions
