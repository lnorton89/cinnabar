; Highlighting for Cinnabar.
;
; Casing is grammar in this language, not convention: the compiler's lexer
; rejects a mis-cased identifier. That is why almost everything below is a
; structural match rather than a name list — an identifier's shape already
; says whether it names a type, a constant, or a binding, with no symbol
; table involved. The one place a name list appears is the built-in type
; grid, which the compiler seeds as symbols rather than keywords.

; ---- comments -------------------------------------------------------------
(line_comment) @comment
(block_comment) @comment
(doc_line_comment) @comment.documentation
(doc_block_comment) @comment.documentation

; ---- literals -------------------------------------------------------------
(integer_literal) @number
(hex_literal) @number
(string_literal) @string
(boolean_literal) @constant.builtin

; ---- declarations ---------------------------------------------------------
(function_signature name: (identifier) @function)
(native_function_declaration name: (identifier) @function)
(call_expression function: (identifier) @function.call)
(call_expression function: (path (identifier) @function.call .))

(module_declaration name: (type_identifier) @module)
(type_declaration name: (type_identifier) @type)
(native_type_declaration name: (type_identifier) @type)
(trait_declaration name: (type_identifier) @type)
(variant_declaration name: (type_identifier) @constructor)
(const_declaration name: (constant_identifier) @constant)
(const_declaration name: (type_identifier) @constant)

(field_declaration name: (identifier) @property)
(field_initializer name: (identifier) @property)
(field_expression field: (identifier) @property)
(parameter name: (identifier) @variable.parameter)
(let_statement name: (identifier) @variable)

; ---- types and values -----------------------------------------------------
(type_identifier) @type
(constant_identifier) @constant

; The built-in grid. These are ordinary PascalCase symbols to the compiler,
; so they are named here rather than lexed as keywords.
((type_identifier) @type.builtin
  (#any-of? @type.builtin
   "Unit" "Bool" "I8" "I16" "I32" "I64" "Isize" "U8" "U16" "U32" "U64" "Usize"
   "Result" "Option" "DivError" "IndexError" "Self"))

((type_identifier) @constant.builtin
  (#any-of? @constant.builtin "Ok" "Err" "Some" "None"))

; ---- keywords -------------------------------------------------------------
[
  "fun" "val" "var" "const" "type" "trait" "impl" "mod" "use" "as" "for" "nat"
] @keyword

[
  "if" "elif" "else" "while" "match" "return" "try" "end"
] @keyword.control

; `break` and `continue` are whole statements in the tree rather than
; keywords inside one, so they are matched as the nodes they are.
(break_statement) @keyword.control
(continue_statement) @keyword.control

(visibility) @keyword.modifier
(impure) @keyword.modifier
"mut" @keyword.modifier

; ---- operators and punctuation --------------------------------------------
[
  "+" "-" "*" "/" "%" "<<" ">>" "&" "|" "^" "==" "!=" "<" ">" "<=" ">=" "&&"
  "||" "!" "=" "=>" "@" ".."
] @operator

[ "(" ")" "[" "]" ] @punctuation.bracket
[ "," ":" ";" "." ] @punctuation.delimiter
