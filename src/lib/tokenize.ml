open Fmt
open Sedlexing
open Spec

exception
  LexError of
    { pos_lnum : int
    ; pos_cnum : int
    }

(* general *)
let blank = [%sedlex.regexp? ' ' | '\t']
let newline = [%sedlex.regexp? '\r' | '\n' | "\r\n"]
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let digit = [%sedlex.regexp? '0' .. '9']

(* comments *)
let comment0_begin = [%sedlex.regexp? "--"]
let comment0_end = [%sedlex.regexp? newline]
let comment1_begin = [%sedlex.regexp? "/-"]
let comment1_end = [%sedlex.regexp? "-/"]

(* delimiters *)
let lparen = [%sedlex.regexp? '(']
let rparen = [%sedlex.regexp? ')']
let lbrack = [%sedlex.regexp? '[']
let rbrack = [%sedlex.regexp? ']']
let lbrace = [%sedlex.regexp? '{']
let rbrace = [%sedlex.regexp? '}']
let langle = [%sedlex.regexp? 10216] (* ⟨ *)
let rangle = [%sedlex.regexp? 10217] (* ⟩ *)
let flq = [%sedlex.regexp? 8249] (* ‹ *)
let frq = [%sedlex.regexp? 8250] (* › *)

(* quantifiers *)
let forall = [%sedlex.regexp? 8704] (* ∀ *)
let exists = [%sedlex.regexp? 8707] (* ∃ *)

(* arrows *)
let leftarrow0 = [%sedlex.regexp? "<-" | 8592] (* ← *)
let leftarrow1 = [%sedlex.regexp? 8656] (* ⇐ *)
let rightarrow0 = [%sedlex.regexp? "->" | 8594] (* → *)
let rightarrow1 = [%sedlex.regexp? "=>" | 8658] (* ⇒ *)
let multimap = [%sedlex.regexp? "-o" | 8888] (* ⊸ *)
let uparrow1 = [%sedlex.regexp? 8657] (* ⇑ *)
let downarrow1 = [%sedlex.regexp? 8659] (* ⇓ *)

(* products *)
let times = [%sedlex.regexp? 215] (* × *)
let otimes = [%sedlex.regexp? 8855] (* ⊗ *)

(* bool *)
let bool_and = [%sedlex.regexp? "&&"]
let bool_or = [%sedlex.regexp? "||"]

(* nat *)
let add = [%sedlex.regexp? '+']
let sub = [%sedlex.regexp? '-']
let mul = [%sedlex.regexp? '*']
let div = [%sedlex.regexp? '/']
let rem = [%sedlex.regexp? '%']
let lte = [%sedlex.regexp? "<="]
let gte = [%sedlex.regexp? ">="]
let lt = [%sedlex.regexp? "<"]
let gt = [%sedlex.regexp? ">"]
let eq = [%sedlex.regexp? "=="]
let neq = [%sedlex.regexp? "!="]

(* string *)
let quote0 = [%sedlex.regexp? "\'"]
let quote1 = [%sedlex.regexp? "\""]
let str_cat = [%sedlex.regexp? '^']

(* list *)
let list_cons = [%sedlex.regexp? "::"]

(* truth *)
let top = [%sedlex.regexp? 8868] (* ⊤ *)
let bot = [%sedlex.regexp? 8869] (* ⊥ *)

(* equality *)
let equal = [%sedlex.regexp? '=']
let assign = [%sedlex.regexp? ":=" | 8788]
let equiv = [%sedlex.regexp? 8801] (* ≡ *)
let negate = [%sedlex.regexp? 172] (* ¬ *)

(* separators *)
let pipe = [%sedlex.regexp? '|']
let dot = [%sedlex.regexp? '.']
let colon = [%sedlex.regexp? ':']
let comma = [%sedlex.regexp? ',']
let semi = [%sedlex.regexp? ';']
let bullet = [%sedlex.regexp? 8226 | 8729] (* • *)

(* sort *)
let sort_u = [%sedlex.regexp? 'U']
let sort_l = [%sedlex.regexp? 'L']

(* prim *)
let prim_stdin = [%sedlex.regexp? "stdin"]
let prim_stdout = [%sedlex.regexp? "stdout"]
let prim_stderr = [%sedlex.regexp? "stderr"]

(* tm *)
let identifier =
  [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_' | '\'')]

let integer = [%sedlex.regexp? Plus digit]
let tm_type0 = [%sedlex.regexp? "Type", lt]
let tm_type1 = [%sedlex.regexp? "Type", flq]
let tm_forall0 = [%sedlex.regexp? "forall", lt]
let tm_forall1 = [%sedlex.regexp? "forall", flq]
let tm_fn = [%sedlex.regexp? "fn"]
let tm_ln = [%sedlex.regexp? "ln"]
let tm_function = [%sedlex.regexp? "function"]
let tm_let = [%sedlex.regexp? "let"]
let tm_in = [%sedlex.regexp? "in"]
let tm_tup = [%sedlex.regexp? "tup"]
let tm_match = [%sedlex.regexp? "match"]
let tm_as = [%sedlex.regexp? "as"]
let tm_with = [%sedlex.regexp? "with"]
let tm_if = [%sedlex.regexp? "if"]
let tm_then = [%sedlex.regexp? "then"]
let tm_else = [%sedlex.regexp? "else"]
let tm_absurd = [%sedlex.regexp? "!!"]
let tm_magic = [%sedlex.regexp? "#magic"]
let tm_io = [%sedlex.regexp? "IO"]
let tm_return = [%sedlex.regexp? "return"]
let tm_mlet = [%sedlex.regexp? "let*"]
let constant0 = [%sedlex.regexp? identifier, lt]
let constant1 = [%sedlex.regexp? identifier, flq]

(* modifiers *)
let mod_program = [%sedlex.regexp? "program"]
let mod_logical = [%sedlex.regexp? "logical"]
let mod_multiplicative = [%sedlex.regexp? "multiplicative"]
let mod_additive = [%sedlex.regexp? "additive"]
let modifier = [%sedlex.regexp? "#["]

(* dcl *)
let dcl_def = [%sedlex.regexp? "def"]
let dcl_inductive = [%sedlex.regexp? "inductive"]
let dcl_where = [%sedlex.regexp? "where"]

let rec filter buf =
  match%sedlex buf with
  | Plus blank -> filter buf
  | Plus newline -> filter buf
  | Plus comment0_begin ->
    filter0 buf;
    filter buf
  | Plus comment1_begin ->
    filter1 buf;
    filter buf
  | _ -> ()

and filter0 buf =
  match%sedlex buf with
  | Plus comment0_end -> ()
  | any -> filter0 buf
  | _ -> ()

and filter1 buf =
  match%sedlex buf with
  | Plus comment1_end -> ()
  | any ->
    filter buf;
    filter1 buf
  | _ -> ()

let rec tokenize buf =
  let _ = filter buf in
  match%sedlex buf with
  (* general *)
  | eof -> EOF
  (* delimiters *)
  | lparen -> LPAREN
  | rparen -> RPAREN
  | lbrack -> LBRACK
  | rbrack -> RBRACK
  | lbrace -> LBRACE
  | rbrace -> RBRACE
  | langle -> LANGLE
  | rangle -> RANGLE
  | flq -> FLQ
  | frq -> FRQ
  (* quantifiers *)
  | forall -> FORALL
  | exists -> EXISTS
  (* arrows *)
  | leftarrow0 -> LEFTARROW0
  | leftarrow1 -> LEFTARROW1
  | rightarrow0 -> RIGHTARROW0
  | rightarrow1 -> RIGHTARROW1
  | multimap -> MULTIMAP
  | uparrow1 -> UPARROW1
  | downarrow1 -> DOWNARROW1
  (* products *)
  | times -> TIMES
  | otimes -> OTIMES
  (* bool *)
  | bool_and -> AND
  | bool_or -> OR
  (* nat *)
  | add -> ADD
  | sub -> SUB
  | mul -> MUL
  | div -> DIV
  | rem -> REM
  | lte -> LTE
  | gte -> GTE
  | lt -> LT
  | gt -> GT
  | eq -> EQEQ
  | neq -> NEQ
  (* string *)
  | quote0 -> CHAR (tokenize_char buf)
  | quote1 -> STRING (tokenize_string buf)
  | str_cat -> STR_CAT
  (* list *)
  | list_cons -> LIST_CONS
  (* truth *)
  | top -> TOP
  | bot -> BOT
  (* equality *)
  | equal -> EQUAL
  | assign -> ASSIGN
  | equiv -> EQUIV
  | negate -> NEGATE
  (* separator *)
  | pipe -> PIPE
  | dot -> DOT
  | colon -> COLON
  | comma -> COMMA
  | semi -> SEMI
  | bullet -> BULLET
  (* sort *)
  | sort_u -> SORT_U
  | sort_l -> SORT_L
  (* prim *)
  | prim_stdin -> PRIM_STDIN
  | prim_stdout -> PRIM_STDOUT
  | prim_stderr -> PRIM_STDERR
  (* tm *)
  | tm_type0 -> TM_TYPE0
  | tm_type1 -> TM_TYPE1
  | tm_forall0 -> TM_FORALL0
  | tm_forall1 -> TM_FORALL1
  | tm_fn -> TM_FN
  | tm_ln -> TM_LN
  | tm_function -> TM_FUNCTION
  | tm_let -> TM_LET
  | tm_in -> TM_IN
  | tm_tup -> TM_TUP
  | tm_match -> TM_MATCH
  | tm_as -> TM_AS
  | tm_with -> TM_WITH
  | tm_if -> TM_IF
  | tm_then -> TM_THEN
  | tm_else -> TM_ELSE
  | tm_absurd -> TM_ABSURD
  | tm_magic -> TM_MAGIC
  | tm_io -> TM_IO
  | tm_return -> TM_RETURN
  | tm_mlet -> TM_MLET
  (* modifiers *)
  | mod_program -> MOD_PROGRAM
  | mod_logical -> MOD_LOGICAL
  | mod_multiplicative -> MOD_MULTIPLICATIVE
  | mod_additive -> MOD_ADDITIVE
  | modifier -> MODIFIER
  (* dcl *)
  | dcl_def -> DCL_DEF
  | dcl_inductive -> DCL_INDUCTIVE
  | dcl_where -> DCL_WHERE
  (* other *)
  | integer ->
    let i = int_of_string (Utf8.lexeme buf) in
    INTEGER i
  | constant0 ->
    let s = Utf8.lexeme buf in
    CONSTANT0 Text.(sub s 0 (length s - 1))
  | constant1 ->
    let s = Utf8.lexeme buf in
    CONSTANT1 Text.(sub s 0 (length s - 1))
  | identifier ->
    let s = Utf8.lexeme buf in
    IDENTIFIER s
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_char0 buf =
  match%sedlex buf with
  | "\\", "\\" -> Char.code '\\'
  | "\\", "\'" -> Char.code '\''
  | "\\", "\"" -> Char.code '\"'
  | "\\", "n" -> Char.code '\n'
  | "\\", "t" -> Char.code '\t'
  | "\\", "b" -> Char.code '\b'
  | "\\", "r" -> Char.code '\r'
  | "\\", " " -> Char.code '\ '
  | "\\", digit, digit, digit ->
    let tok = Utf8.lexeme buf in
    let tok = Scanf.unescaped tok in
    Char.code (String.get tok 0)
  | any ->
    let tok = Utf8.lexeme buf in
    Char.code (String.get tok 0)
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_char buf =
  let ls = tokenize_char0 buf in
  match%sedlex buf with
  | quote0 -> ls
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_string buf =
  match%sedlex buf with
  | quote1 -> []
  | _ ->
    let ls = tokenize_char0 buf in
    let lss = tokenize_string buf in
    ls :: lss
