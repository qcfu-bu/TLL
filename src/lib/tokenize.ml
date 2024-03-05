open Fmt
open Sedlexing
open Spec

let utf8_len s =
  Camomile.UTF8.length s

let utf8_sub s start offset =
  let open Camomile.UTF8 in
  let buf = Buf.create offset in
  for x = start to start + offset - 1 do
    Buf.add_char buf (get s x)
  done;
  Buf.contents buf

exception
  LexError of
    { pos_lnum : int
    ; pos_cnum : int
    }

(* general *)
let blank = [%sedlex.regexp? ' ' | '\t' | "\r" | '\n']
let newline = [%sedlex.regexp? '\r' | '\n' | "\r\n"]
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let digit = [%sedlex.regexp? '0' .. '9']
let integer = [%sedlex.regexp? Plus digit]

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
let lt = [%sedlex.regexp? '<']
let gt = [%sedlex.regexp? '>']
let flq = [%sedlex.regexp? 8249] (* ‹ *)
let frq = [%sedlex.regexp? 8250] (* › *)
let qlparen = [%sedlex.regexp? "?("]
let qlbrace = [%sedlex.regexp? "?{"]
let rlbrack = [%sedlex.regexp? "]["]
let plbrack = [%sedlex.regexp? ")["]

(* quantifiers *)
let forall = [%sedlex.regexp? "forall" | 8704] (* ∀ *)
let exists = [%sedlex.regexp? 8707] (* ∃ *)

(* arrows *)
let leftarrow0 = [%sedlex.regexp? "<-" | 8592] (* ← *)
let leftarrow1 = [%sedlex.regexp? 8656] (* ⇐ *)
let rightarrow0 = [%sedlex.regexp? "->" | 8594] (* → *)
let rightarrow1 = [%sedlex.regexp? "=>" | 8658] (* ⇒ *)
let dot_rarrow0 = [%sedlex.regexp? ".->" | (".", 8594)] (* .→ *)
let multimap = [%sedlex.regexp? "-o" | 8888] (* ⊸ *)
let uparrow1 = [%sedlex.regexp? 8657] (* ⇑ *)
let downarrow1 = [%sedlex.regexp? 8659] (* ⇓ *)

(* operators *)
let op_symbol =
  [%sedlex.regexp?
      ( '+' | '-' | '*' | '/' | '\\' | '%' | '<' | '>' | '=' | '!' | '&' | '~'
      | '^' | '|' | ':' | ';' | '@' | '`' | 215 | 8855 )]

let op_mul = [%sedlex.regexp? '*', Star op_symbol]
let op_times = [%sedlex.regexp? 215, Star op_symbol] (* × *)
let op_otimes = [%sedlex.regexp? 8855, Star op_symbol] (* ⊗ *)
let op_div = [%sedlex.regexp? '/', Star op_symbol]
let op_mod = [%sedlex.regexp? '%', Star op_symbol]
let op_add = [%sedlex.regexp? '+', Star op_symbol]
let op_sub = [%sedlex.regexp? '-', Star op_symbol]
let op_lt = [%sedlex.regexp? "<", Plus op_symbol]
let op_gt = [%sedlex.regexp? ">", Plus op_symbol]
let op_eq = [%sedlex.regexp? "=", Star op_symbol]
let op_ex = [%sedlex.regexp? "!", Star op_symbol]
let op_and = [%sedlex.regexp? "&", Star op_symbol]
let op_sim = [%sedlex.regexp? "~", Star op_symbol]
let op_cat = [%sedlex.regexp? '^', Star op_symbol]
let op_or = [%sedlex.regexp? "|", Plus op_symbol]
let op_colon = [%sedlex.regexp? ":", Plus op_symbol]
let op_semi = [%sedlex.regexp? ";", Plus op_symbol]
let op_at = [%sedlex.regexp? "@", Star op_symbol]
let op_tic = [%sedlex.regexp? "`", Star op_symbol]

(* string *)
let quote0 = [%sedlex.regexp? "\'"]
let quote1 = [%sedlex.regexp? "\""]

(* truth *)
let top = [%sedlex.regexp? 8868] (* ⊤ *)
let bot = [%sedlex.regexp? 8869] (* ⊥ *)

(* assign *)
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

(* identifiers *)
let identifier =
  [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_' | '\'')]

let constant0 = [%sedlex.regexp? identifier, lt]
let constant1 = [%sedlex.regexp? identifier, flq]
let at_identifier = [%sedlex.regexp? "@", identifier]
let at_constant0 = [%sedlex.regexp? "@", constant0]
let at_constant1 = [%sedlex.regexp? "@", constant1]
let hole = [%sedlex.regexp? "%", integer]
let hbrack = [%sedlex.regexp? "%", integer, "["]

(* term *)
let tm_type0 = [%sedlex.regexp? "Type", lt]
let tm_type1 = [%sedlex.regexp? "Type", flq]
let tm_forall0 = [%sedlex.regexp? "forall", lt]
let tm_forall1 = [%sedlex.regexp? "forall", flq]
let tm_fn = [%sedlex.regexp? "fn"]
let tm_ln = [%sedlex.regexp? "ln"]
let tm_fun = [%sedlex.regexp? "fun"]
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
let tm_magic0 = [%sedlex.regexp? "#magic"]
let tm_magic1 = [%sedlex.regexp? "#magic["]
let tm_io = [%sedlex.regexp? "IO"]
let tm_return = [%sedlex.regexp? "return"]
let tm_mlet = [%sedlex.regexp? "let*"]

(* modifiers *)
let mod_program = [%sedlex.regexp? "program"]
let mod_logical = [%sedlex.regexp? "logical"]
let modifier = [%sedlex.regexp? "#["]

(* primitive types *)
let prim_int_t = [%sedlex.regexp? "int"] 
let prim_char_t = [%sedlex.regexp? "char"] 
let prim_string_t = [%sedlex.regexp? "string"] 

(* primitive terms *)
let prim_int = [%sedlex.regexp? integer]

(* primitive operators *)
let prim_neg = [%sedlex.regexp? "__neg__"]
let prim_add = [%sedlex.regexp? "__add__"]
let prim_sub = [%sedlex.regexp? "__sub__"]
let prim_mul = [%sedlex.regexp? "__mul__"]
let prim_div = [%sedlex.regexp? "__div__"]
let prim_mod = [%sedlex.regexp? "__mod__"]
let prim_lte = [%sedlex.regexp? "__lte__"]
let prim_gte = [%sedlex.regexp? "__gte__"]
let prim_lt = [%sedlex.regexp? "__lt__"]
let prim_gt = [%sedlex.regexp? "__gt__"]
let prim_eq = [%sedlex.regexp? "__eq__"]
let prim_chr = [%sedlex.regexp? "__chr__"]
let prim_ord = [%sedlex.regexp? "__ord__"]
let prim_push = [%sedlex.regexp? "__push__"]
let prim_cat = [%sedlex.regexp? "__cat__"]
let prim_size = [%sedlex.regexp? "__size__"]
let prim_indx = [%sedlex.regexp? "__indx_"]

(* primitive sessions *)
let prim_proto = [%sedlex.regexp? "proto"]
let prim_end = [%sedlex.regexp? "end"]
let prim_ch = [%sedlex.regexp? "ch"]
let prim_hc = [%sedlex.regexp? "hc"]

(* primitive effects *)
let prim_print = [%sedlex.regexp? "print"]
let prim_prerr = [%sedlex.regexp? "prerr"]
let prim_readln = [%sedlex.regexp? "readln"]
let prim_fork = [%sedlex.regexp? "fork"]
let prim_send = [%sedlex.regexp? "send"]
let prim_recv = [%sedlex.regexp? "recv"]
let prim_close = [%sedlex.regexp? "close"]

(* dcl *)
let dcl_def = [%sedlex.regexp? "def"]
let dcl_lemma = [%sedlex.regexp? "lemma"]
let dcl_theorem = [%sedlex.regexp? "theorem"]
let dcl_inductive = [%sedlex.regexp? "inductive"]
let dcl_where = [%sedlex.regexp? "where"]
let dcl_tmpl = [%sedlex.regexp? "tmpl"]
let dcl_impl = [%sedlex.regexp? "impl"]
let dcl_extern = [%sedlex.regexp? "extern"]
let dcl_notation = [%sedlex.regexp? "notation"]

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
  | dot, lbrack -> DLBRACK
  | rlbrack -> RLBRACK
  | lt -> LT
  | gt -> GT
  | flq -> FLQ
  | frq -> FRQ
  | qlparen -> QLPAREN
  | qlbrace -> QLBRACE
  (* quantifiers *)
  | forall -> FORALL
  | exists -> EXISTS
  (* arrows *)
  | leftarrow0 -> LEFTARROW0
  | leftarrow1 -> LEFTARROW1
  | rightarrow0 -> RIGHTARROW0
  | rightarrow1 -> RIGHTARROW1
  | dot_rarrow0 -> DOT_RARROW0
  | multimap -> MULTIMAP
  | uparrow1 -> UPARROW1
  | downarrow1 -> DOWNARROW1
  (* equality *)
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
  (* tm *)
  | tm_type0 -> TM_TYPE0
  | tm_type1 -> TM_TYPE1
  | tm_forall0 -> TM_FORALL0
  | tm_forall1 -> TM_FORALL1
  | tm_fn -> TM_FN
  | tm_ln -> TM_LN
  | tm_fun -> TM_FUN
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
  | tm_magic0 -> TM_MAGIC0
  | tm_magic1 -> TM_MAGIC1
  | tm_io -> TM_IO
  | tm_return -> TM_RETURN
  | tm_mlet -> TM_MLET
  (* modifiers *)
  | mod_program -> MOD_PROGRAM
  | mod_logical -> MOD_LOGICAL
  | modifier -> MODIFIER
  (* dcl *)
  | dcl_def -> DCL_DEF
  | dcl_lemma -> DCL_LEMMA
  | dcl_theorem -> DCL_THEOREM
  | dcl_inductive -> DCL_INDUCTIVE
  | dcl_where -> DCL_WHERE
  | dcl_tmpl -> DCL_TMPL
  | dcl_impl -> DCL_IMPL
  | dcl_extern -> DCL_EXTERN
  | dcl_notation -> DCL_NOTATION
  (* operators *)
  | op_mul -> OP_MUL (Utf8.lexeme buf)
  | op_times -> OP_TIMES (Utf8.lexeme buf)
  | op_otimes -> OP_OTIMES (Utf8.lexeme buf)
  | op_div -> OP_DIV (Utf8.lexeme buf)
  | op_mod -> OP_MOD (Utf8.lexeme buf)
  | op_add -> OP_ADD (Utf8.lexeme buf)
  | op_sub -> OP_SUB (Utf8.lexeme buf)
  | op_lt -> OP_LT (Utf8.lexeme buf)
  | op_gt -> OP_GT (Utf8.lexeme buf)
  | op_eq -> OP_EQ (Utf8.lexeme buf)
  | op_ex -> OP_EX (Utf8.lexeme buf)
  | op_and -> OP_AND (Utf8.lexeme buf)
  | op_or -> OP_OR (Utf8.lexeme buf)
  | op_sim -> OP_SIM (Utf8.lexeme buf)
  | op_cat -> OP_CAT (Utf8.lexeme buf)
  | op_colon -> OP_COLON (Utf8.lexeme buf)
  | op_semi -> OP_SEMI (Utf8.lexeme buf)
  | op_at -> OP_AT (Utf8.lexeme buf)
  | op_tic -> OP_TIC (Utf8.lexeme buf)
  (* primitives types *)
  | prim_int_t -> PRIM_INT_T
  | prim_char_t -> PRIM_CHAR_T
  | prim_string_t -> PRIM_STRING_T
  (* primitives terms *)
  | prim_int -> PRIM_INT (int_of_string (Utf8.lexeme buf))
  | quote0 -> PRIM_CHAR (tokenize_char buf)
  | quote1 ->
    let cs = tokenize_string buf in
    PRIM_STRING (String.of_seq (List.to_seq cs))
  (* primitive operators *)
  | prim_neg -> PRIM_NEG
  | prim_add -> PRIM_ADD
  | prim_sub -> PRIM_SUB
  | prim_mul -> PRIM_MUL
  | prim_div -> PRIM_DIV
  | prim_mod -> PRIM_MOD
  | prim_lte -> PRIM_LTE
  | prim_gte -> PRIM_GTE
  | prim_lt -> PRIM_LT
  | prim_gt -> PRIM_GT
  | prim_eq -> PRIM_EQ
  | prim_chr -> PRIM_CHR
  | prim_ord -> PRIM_ORD
  | prim_push -> PRIM_PUSH
  | prim_cat -> PRIM_CAT
  | prim_size -> PRIM_SIZE
  | prim_indx -> PRIM_INDX
  (* primitive sessions *)
  | prim_proto -> PRIM_PROTO
  | prim_end -> PRIM_END
  | prim_ch, langle -> PRIM_CH
  | prim_hc, langle -> PRIM_HC
  (* primitive effects *)
  | prim_print -> PRIM_PRINT
  | prim_prerr -> PRIM_PRERR
  | prim_readln -> PRIM_READLN
  | prim_fork -> PRIM_FORK
  | prim_send -> PRIM_SEND
  | prim_recv -> PRIM_RECV
  | prim_close -> PRIM_CLOSE
  (* identifiers *)
  | identifier -> ID (Utf8.lexeme buf)
  | constant0 ->
    let s = Utf8.lexeme buf in
    CONST0 (utf8_sub s 0 (utf8_len s - 1))
  | constant1 ->
    let s = Utf8.lexeme buf in
    CONST1 (utf8_sub s 0 (utf8_len s - 1))
  | at_constant0 ->
    let s = Utf8.lexeme buf in
    AT_CONSTANT0 (utf8_sub s 1 (utf8_len s - 2))
  | at_constant1 ->
    let s = Utf8.lexeme buf in
    AT_CONSTANT1 (utf8_sub s 1 (utf8_len s - 2))
  | at_identifier ->
    let s = Utf8.lexeme buf in
    AT_ID (utf8_sub s 1 (utf8_len s - 1))
  | hole ->
    let s = Utf8.lexeme buf in
    let s = utf8_sub s 1 (utf8_len s - 1) in
    HOLE (int_of_string s)
  | _ ->
    let pos = fst (lexing_positions buf) in
    raise (LexError { pos_lnum = pos.pos_lnum; pos_cnum = pos.pos_cnum })

and tokenize_char0 buf =
  match%sedlex buf with
  | "\\", "\\" -> '\\'
  | "\\", "\'" -> '\''
  | "\\", "\"" -> '\"'
  | "\\", "n" -> '\n'
  | "\\", "t" -> '\t'
  | "\\", "b" -> '\b'
  | "\\", "r" -> '\r'
  | "\\", " " -> '\ '
  | "\\", digit, digit, digit ->
    let tok = Utf8.lexeme buf in
    let tok = Scanf.unescaped tok in
    String.get tok 0
  | any ->
    let tok = Utf8.lexeme buf in
    String.get tok 0
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
    let c = tokenize_char0 buf in
    let cs = tokenize_string buf in
    c :: cs
