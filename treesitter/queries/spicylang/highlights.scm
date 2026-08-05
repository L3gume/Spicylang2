; Comments
(comment) @comment

; Keywords
[
  "let"
  "in"
  "if"
  "then"
  "else"
  "match"
  "type"
  "enum"
  "list"
] @keyword

; Operators
[
  "\\"
  "=>"
  "::"
  "||"
  "&&"
  "^"
  "=="
  "!="
  "<"
  ">"
  "<="
  ">="
  "+"
  "-"
  "*"
  "/"
  "%"
  "!"
] @operator

; Types
(builtin_type) @type.builtin

(list_type) @type

(type_var) @type.parameter

(app_type
  (identifier) @type)

(type_arg
  (identifier) @type)

(type_header
  name: (identifier) @type.definition)

(type_parameter_list
  (type_var) @type.parameter)

(variant
  name: (identifier) @type)

; Bindings and definitions
(let_statement
  name: (identifier) @variable)

(let_expression
  name: (identifier) @variable)

(binding
  name: (identifier) @variable.parameter)

; Variables
(variable) @variable

; Function calls
(application_expression
  function: (variable) @function)

(application_expression
  function: (application_expression
    (variable) @function))

; Literals
(integer_literal) @number
(float_literal) @number.float
(string_literal) @string
(boolean_literal) @boolean
(unit) @constant.builtin

; Punctuation
[
  "("
  ")"
  "["
  "]"
  "{"
  "}"
] @punctuation.bracket

[
  ","
  ";"
  ":"
  "|"
] @punctuation.delimiter
