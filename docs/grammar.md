# Grammar

This document describes the concrete syntax of SpicyLang as defined in
`src/grammar.lalrpop`. It is written in extended Backus-Naur form (EBNF) with
the following notation:

| Notation | Meaning |
|----------|---------|
| `:=` | definition |
| `\|` | alternation |
| `[ x ]` | optional `x` (zero or one) |
| `{ x }` | zero or more `x` |
| `{ x }+` | one or more `x` |
| `"lit"` | a terminal (literal text) |
| `⟦ … ⟧` | a regular expression |

Where LALRPOP productions carry semantic actions (building an AST node, e.g.
`ENode::Application`), the corresponding EBNF alternative is annotated with the
node it constructs.

---

## Lexical grammar

### Whitespace and comments

```
whitespace  := ⟦\s+⟧
comment     := "#" ⟦[^\n\r]*⟧
```

Whitespace and `#`-prefixed single-line comments are skipped. (The grammar file
refers to these as `//` comments in one stale comment, but the actual pattern is
`#`.)

### Identifiers

```
name := ⟦[a-zA-Z_][a-zA-Z0-9_]*⟧
```

Identifiers start with a letter or underscore and continue with letters, digits,
or underscores. A bare `_` is therefore a valid identifier; it is conventionally
used as a wildcard in `match` patterns.

Type variables are written with a leading apostrophe:

```
type_var := "'" name
```

### Literals

```
literal := int | float | "true" | "false" | string | char | "()"
int     := ⟦[0-9]+⟧
float   := ⟦[0-9]+\.[0-9]+⟧
string  := ⟦"(?:\\.|[^"\\\n\r])*"⟧
char    := ⟦'(\\(u\{[^}]*\}|x[0-9a-fA-F]{2}|.)|[^'\\\n\r])'⟧
```

* `int` and `float` have no sign — negation is the unary `-` operator.
* Strings support escapes: `\X` (single escaped char), `\xHH` (hex byte), and
  `\u{...}` (Unicode scalar).
* Char literals support the plain char or escapes `\c`, `\xHH`, `\u{...}`.
* `()` is the unit literal.

---

## Syntax

```
program := { stmt ";" } [ stmt ]
```

### Statements

```
stmt := type_decl | block_stmt
```

#### Type declarations (top level only)

```
type_decl := "type" type_header type                         (alias)
           | "enum" type_header { variant "|" } [ variant ]  (enum)
           | "record" type_header "{" typed_binding { "," typed_binding } "}"
                                                              (record)

type_header := name [ "(" type_var { "," type_var } ")" ] "="

variant := name
         | name "(" type { "," type } ")"

typed_binding := name ":" type
```

A `record` or `enum` requires at least one field/variant (a comma- or pipe-
separated non-empty list).

#### Block statements

```
block_stmt := "let" name ":" type "=" expr    (typed declaration)
            | "let" name "=" expr             (inferred declaration)
            | expr                            (expression statement)

blk_body := { block_stmt ";" }
```

### Types

```
type := type_base
      | type_base "=>" type          (function type, right-associative)

type_base := builtin_type
           | app_type
           | type_var
           | "list" type_base
           | "(" type ")"

builtin_type := "int" | "bool" | "float" | "str" | "()"

app_type := name
          | app_type app_arg         (enum application, left-associative)

app_arg := builtin_type
         | name
         | type_var
         | "list" app_arg
         | "(" type ")"
```

Enum applications are space-separated and greedy/left-associative, mirroring
function application in the expression grammar. Because an `app_arg` that is a
bare `name` is a constructor, nesting an application requires parens:
`option (maybe int)`.

### Expressions

```
expr := abs_expr
      | "let" name "=" expr "in" expr          (Let)
      | "if" expr "then" expr "else" expr      (IfElse)
      | "match" cons_expr "|" { match_case "|" } [ match_case ]
                                                (Match)
      | cons_expr

match_case := cons_expr "=>" cons_expr
```

#### Lists and cons

```
cons_expr := expr_base
           | cons_operand "::" cons_expr       (Cons, right-associative)

cons_operand := unary_expr | block
```

#### Base expressions

```
expr_base := log_expr
           | name record_body                  (Record construction)
           | with_operand "with" record_body   (With update)
           | block

with_operand := postfix_expr | block

block := "{" blk_body expr "}"                 (Block)

record_body := "{" field_assn { "," field_assn } "}"

field_assn := name ":" expr
```

#### Abstractions

```
abs_expr := "\" { binding }+ "=>" expr

binding := name
         | "(" typed_binding ")"
```

Multiple binders are sugar for nested abstractions: `\x y z => e` desugars to
`\x => \y => \z => e`.

#### Operators (precedence cascade)

```
log_expr := cmp_expr
          | log_expr "||" cmp_expr             (Logical or)
          | log_expr "&&" cmp_expr             (Logical and)
          | log_expr "^"  cmp_expr             (Logical xor)

cmp_expr := add_expr
          | add_expr "==" add_expr
          | add_expr "!=" add_expr
          | add_expr "<"  add_expr
          | add_expr ">"  add_expr
          | add_expr "<=" add_expr
          | add_expr ">=" add_expr

add_expr := mul_expr
          | add_expr "+" mul_expr              (Arithmetic plus)
          | add_expr "-" mul_expr              (Arithmetic minus)

mul_expr := unary_expr
          | mul_expr "*" unary_expr            (Arithmetic times)
          | mul_expr "/" unary_expr            (Arithmetic div)
          | mul_expr "%" unary_expr            (Arithmetic mod)

unary_expr := app_expr
            | "-" unary_expr                   (Unary negate)
            | "!" unary_expr                   (Unary not)

app_expr := atom
          | app_expr atom                      (Application, left-associative)

atom := literal
      | "[" "]"
      | "[" expr { "," expr } "]"
      | postfix_expr

postfix_expr := name                           (Variable)
              | postfix_expr "." name          (FieldAccess)
              | "(" expr ")"
```

---

## Precedence and associativity

From lowest to highest binding:

| Level | Operators / forms | Associativity |
|-------|-------------------|---------------|
| `expr` | `let … in`, `if … then … else`, `match`, lambda | — |
| `cons_expr` | `::` | right |
| `expr_base` | record literal, `with`, block | — |
| `log_expr` | `\|\|`, `&&`, `^` | left |
| `cmp_expr` | `==`, `!=`, `<`, `>`, `<=`, `>=` | (non-associative) |
| `add_expr` | `+`, `-` | left |
| `mul_expr` | `*`, `/`, `%` | left |
| `unary_expr` | unary `-`, `!` | (prefix) |
| `app_expr` | function application (juxtaposition) | left |
| `atom` | literals, lists | — |
| `postfix_expr` | `.` field access | left |

Function application binds tighter than all binary operators, so `f x + 1`
parses as `(f x) + 1`. Field access binds tighter than application, so `f x.y`
parses as `f (x.y)`.

---

## Parentheses are required in these cases

The grammar deliberately keeps several operands "non-binary" so the parse stays
LALR(1) and unambiguous. A binary (or non-atom) expression must be parenthesised
in the following positions:

* Left operand of `::` — `(a + b) :: c`.
* Left operand of `with` — `(f x) with { … }`, since `with_operand` is only
  `postfix_expr` or a block.
* Field access on a non-postfix expression — `(f x).y`, `(a + b).y`.
* A record literal used as a function argument or field access target —
  `f (Person { … })`, `(Person { … }).name`.

Because `name { … }` is a record literal, a `name` immediately followed by `{`
is always parsed as a record literal, never as the application of `name` to a
block. Applying a function to a block requires parens: `f ({ … })`.

A block (`{ … }`) is only valid as a standalone expression (in `expr_base`,
`cons_operand`, or `with_operand`); it is not an `atom`, so it cannot appear as a
function argument without parens.
