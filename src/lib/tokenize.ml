open Fmt
open Util
open Sedlexing
open Parser0

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

(* quantifiers *)
let forall = [%sedlex.regexp? 8704] (* ∀ *)
let exists = [%sedlex.regexp? 8707] (* ∃ *)

(* arrows *)
let leftarrow0 = [%sedlex.regexp? 8592] (* ← *)
let leftarrow1 = [%sedlex.regexp? 8656] (* ⇐ *)
let rightarrow0 = [%sedlex.regexp? 8594] (* → *)
let rightarrow1 = [%sedlex.regexp? 8658] (* ⇒ *)
let multimap = [%sedlex.regexp? 8888] (* ⊸ *)
let uparrow1 = [%sedlex.regexp? 8657] (* ⇑ *)
let downarrow1 = [%sedlex.regexp? 8659] (* ⇓ *)

(* products *)
let times = [%sedlex.regexp? 215] (* × *)
let otimes = [%sedlex.regexp? 8855] (* ⊗ *)

(* arithemtic *)
let arith_add = [%sedlex.regexp? '+']
let arith_sub = [%sedlex.regexp? '-']
let arith_mul = [%sedlex.regexp? '*']
let arith_div = [%sedlex.regexp? '/']
let arith_mod = [%sedlex.regexp? '%']
let arith_lte = [%sedlex.regexp? "<="]
let arith_gte = [%sedlex.regexp? ">="]
let arith_lt = [%sedlex.regexp? "<"]
let arith_gt = [%sedlex.regexp? ">"]
let arith_eq = [%sedlex.regexp? "=="]
let arith_neq = [%sedlex.regexp? "!="]

(* boolean *)
let bool_and = [%sedlex.regexp? "&&"]
let bool_or = [%sedlex.regexp? "||"]

(* string *)
let quote0 = [%sedlex.regexp? "\'"]
let quote1 = [%sedlex.regexp? "\""]
let str_cat = [%sedlex.regexp? '^']

(* list *)
let ulist_cons = [%sedlex.regexp? "::"]
let llist_cons = [%sedlex.regexp? ";;"]

(* equality *)
let equal = [%sedlex.regexp? '=']
let equiv = [%sedlex.regexp? 8801] (* ≡ *)
let negate = [%sedlex.regexp? 172] (* ¬ *)

(* separators *)
let pipe = [%sedlex.regexp? '|']
let dot = [%sedlex.regexp? '.']
let colon = [%sedlex.regexp? ':']
let comma = [%sedlex.regexp? ',']
let semi = [%sedlex.regexp? ';']
let bullet = [%sedlex.regexp? 8226] (* • *)

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
let tm_fn = [%sedlex.regexp? "fn"]
let tm_ln = [%sedlex.regexp? "ln"]
let tm_let = [%sedlex.regexp? "let"]
let tm_in = [%sedlex.regexp? "in"]
let tm_match = [%sedlex.regexp? "match"]
let tm_with = [%sedlex.regexp? "with"]
let tm_if = [%sedlex.regexp? "if"]
let tm_then = [%sedlex.regexp? "then"]
let tm_else = [%sedlex.regexp? "else"]
let tm_refl = [%sedlex.regexp? "refl"]
let tm_rew = [%sedlex.regexp? "rew"]
let tm_io = [%sedlex.regexp? "IO"]
let tm_return = [%sedlex.regexp? "return"]
let tm_proto = [%sedlex.regexp? "proto"]
let tm_end = [%sedlex.regexp? "end"]
let tm_ch = [%sedlex.regexp? "ch", langle]
let tm_hc = [%sedlex.regexp? "hc", langle]
let tm_open = [%sedlex.regexp? "open"]
let tm_fork = [%sedlex.regexp? "fork"]
let tm_recv = [%sedlex.regexp? "recv"]
let tm_send = [%sedlex.regexp? "send"]
let tm_close = [%sedlex.regexp? "close"]

(* dcl *)
let dcl_program = [%sedlex.regexp? "program"]
let dcl_logical = [%sedlex.regexp? "logical"]
let dcl_inductive = [%sedlex.regexp? "inductive"]

(* dcons *)
let dcons_of = [%sedlex.regexp? "of"]

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
  (* arithmetic *)
  | arith_add -> ARITH_ADD
  | arith_sub -> ARITH_SUB
  | arith_mul -> ARITH_MUL
  | arith_div -> ARITH_DIV
  | arith_mod -> ARITH_MOD
  | arith_lte -> ARITH_LTE
  | arith_gte -> ARITH_GTE
  | arith_lt -> ARITH_LT
  | arith_gt -> ARITH_GT
  | arith_eq -> ARITH_EQ
  | arith_neq -> ARITH_NEQ
  (* boolean *)
  | bool_and -> BOOL_AND
  | bool_or -> BOOL_OR
  (* string *)
  | quote0 -> ASCII (tokenize_ascii buf)
  | quote1 -> STRING (tokenize_string buf)
  | str_cat -> STR_CAT
  (* list *)
  | ulist_cons -> ULIST_CONS
  | llist_cons -> LLIST_CONS
  (* equality *)
  | equal -> EQUAL
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
  | tm_fn -> TM_FN
  | tm_ln -> TM_LN
  | tm_let -> TM_LET
  | tm_in -> TM_IN
  | tm_match -> TM_MATCH
  | tm_with -> TM_WITH
  | tm_if -> TM_IF
  | tm_then -> TM_THEN
  | tm_else -> TM_ELSE
  | tm_refl -> TM_REFL
  | tm_rew -> TM_REW
  | tm_io -> TM_IO
  | tm_return -> TM_RETURN
  | tm_proto -> TM_PROTO
  | tm_end -> TM_END
  | tm_ch -> TM_CH
  | tm_hc -> TM_HC
  | tm_open -> TM_OPEN
  | tm_fork -> TM_FORK
  | tm_recv -> TM_RECV
  | tm_send -> TM_SEND
  | tm_close -> TM_CLOSE
  (* dcl *)
  | dcl_program -> DCL_PROGRAM
  | dcl_logical -> DCL_LOGICAL
  | dcl_inductive -> DCL_INDUCTIVE
  (* dcons *)
  | dcons_of -> DCONS_OF
  (* other *)
  | integer ->
    let i = int_of_string (Utf8.lexeme buf) in
    INTEGER i
  | identifier ->
    let s = Utf8.lexeme buf in
    IDENTIFIER s
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_ascii0 buf =
  match%sedlex buf with
  | "\\", "\\" -> bits_of_char '\\'
  | "\\", "\'" -> bits_of_char '\''
  | "\\", "\"" -> bits_of_char '\"'
  | "\\", "n" -> bits_of_char '\n'
  | "\\", "t" -> bits_of_char '\t'
  | "\\", "b" -> bits_of_char '\b'
  | "\\", "r" -> bits_of_char '\r'
  | "\\", " " -> bits_of_char '\ '
  | "\\", digit, digit, digit ->
    let tok = Utf8.lexeme buf in
    let tok = Scanf.unescaped tok in
    bits_of_char (String.get tok 0)
  | any ->
    let tok = Utf8.lexeme buf in
    bits_of_char (String.get tok 0)
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_ascii buf =
  let ls = tokenize_ascii0 buf in
  match%sedlex buf with
  | quote0 -> ls
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_string buf =
  match%sedlex buf with
  | quote1 -> []
  | _ ->
    let ls = tokenize_ascii0 buf in
    let lss = tokenize_string buf in
    ls :: lss
