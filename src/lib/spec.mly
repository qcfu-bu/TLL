%token EOF

// delimiters
%token LPAREN  // (
%token RPAREN  // )
%token LBRACK  // [
%token RBRACK  // ]
%token LBRACE  // {
%token RBRACE  // {
%token LANGLE  // ⟨
%token RANGLE  // ⟩
%token LT      // <
%token GT      // >
%token FLQ     // ‹
%token FRQ     // ›
%token QLPAREN // ?(
%token QLBRACE // ?{
%token DLBRACK  // .[
%token RLBRACK  // ][

// quantifiers
%token FORALL   // ∀
%token EXISTS   // ∃

// arrows
%token LEFTARROW0  // ←
%token LEFTARROW1  // ⇐
%token RIGHTARROW0 // →
%token RIGHTARROW1 // ⇒
%token MULTIMAP    // ⊸
%token UPARROW1    // ⇑
%token DOWNARROW1  // ⇓
%right RIGHTARROW0
%right MULTIMAP

%token AT     // @
%right TIMES
%right OTIMES

// unit
%token TOP

// operators
%token<string> OP_MUL    // * infixl
%token<string> OP_TIMES  // × infixr
%token<string> OP_OTIMES // ⊗ infixr
%token<string> OP_DIV    // / infixl
%token<string> OP_REM    // % infixl
%token<string> OP_ADD    // + infixl
%token<string> OP_SUB    // - infixl
%token<string> OP_LT     // < infixl
%token<string> OP_GT     // > infixl
%token<string> OP_EQ     // = infixl
%token<string> OP_EX     // ! infixl
%token<string> OP_AND    // & infixl
%token<string> OP_OR     // | infixl
%token<string> OP_SIM    // ~ prefix
%token<string> OP_CAT    // ^ infixl
%token<string> OP_COLON  // : infixr
%token<string> OP_SEMI   // : infixr
%token<string> OP_AT     // @ infixr
%token<string> OP_TIC    // ` prefix

%right OP_SEMI
%right OP_AT
%right OP_COLON
%left OP_OR
%left OP_AND
%left OP_EQ OP_EX
%left OP_LT OP_GT LT GT
%left OP_ADD OP_SUB
%left OP_MUL OP_DIV OP_REM
%right OP_TIMES OP_OTIMES
%left OP_CAT
%nonassoc OP_SIM OP_TIC

// bottom
%token BOT // ⊥

// assign
%token ASSIGN // :=
%token EQUIV  // ≡
%token NEGATE // ¬
%left EQUIV

// separators
%token PIPE   // |
%token DOT    // .
%token COLON  // :
%token COMMA  // ,
%token SEMI   // ;
%token BULLET // •
%right SEMI

// sort
%token SORT_U // U
%token SORT_L // L

// identifier
%token<int> INTEGER          // 123
%token<string> ID            // foo
%token<string> CONST0        // foo<
%token<string> CONST1        // foo‹
%token<string> AT_ID         // @foo
%token<string> AT_CONSTANT0  // @foo<
%token<string> AT_CONSTANT1  // @foo‹
%token<int> HOLE             // %1

// tm
%token TM_TYPE0    // Type<
%token TM_TYPE1    // Type‹
%token TM_FORALL0  // forall<
%token TM_FORALL1  // forall‹
%token TM_FN       // fn
%token TM_LN       // ln
%token TM_FUN      // fun
%token TM_LET      // let
%token TM_IN       // in
%token TM_EXISTS   // exists
%token TM_TUP      // tup
%token TM_MATCH    // match
%token TM_AS       // as
%token TM_WITH     // with
%token TM_IF       // if
%token TM_THEN     // then
%token TM_ELSE     // else
%token TM_REFL     // refl
%token TM_ABSURD   // !!
%token TM_MAGIC0   // #magic
%token TM_MAGIC1   // #magic[
%token TM_IO       // IO
%token TM_RETURN   // return
%token TM_MLET     // let*

// primitive types
%token PRIM_INT_T      // int
%token PRIM_CHAR_T     // char
%token PRIM_STRING_T   // string

// primitive terms
%token <int>PRIM_INT       // 123
%token <char>PRIM_CHAR     // 'a'
%token <string>PRIM_STRING // "abc"

// primitive operators
%token PRIM_NEG   // __neg__
%token PRIM_ADD   // __add__
%token PRIM_SUB   // __sub__
%token PRIM_MUL   // __mul__
%token PRIM_DIV   // __div__
%token PRIM_REM   // __rem__
%token PRIM_LTE   // __lte__
%token PRIM_GTE   // __gte__
%token PRIM_LT    // __lt__
%token PRIM_GT    // __gt__
%token PRIM_EQ    // __eq__
%token PRIM_CHR   // __chr__
%token PRIM_ORD   // __ord__
%token PRIM_PUSH  // __push__
%token PRIM_CAT   // __cat__
%token PRIM_SIZE  // __size__
%token PRIM_INDX  // __indx__

// primitive sessions
%token PRIM_PROTO     // proto
%token PRIM_END       // end
%token PRIM_CH        // ch⟨
%token PRIM_HC        // hc⟨

// primitive effects
%token PRIM_PRINT     // print
%token PRIM_PRERR     // prerr
%token PRIM_READLN    // readln
%token PRIM_FORK      // fork
%token PRIM_SEND      // send
%token PRIM_RECV      // recv
%token PRIM_CLOSE     // close

// modifiers
%token MOD_PROGRAM        // program
%token MOD_LOGICAL        // logical
%token MODIFIER           // #[

// dcl
%token DCL_DEF            // def
%token DCL_INDUCTIVE      // inductive
%token DCL_WHERE          // where
%token DCL_TMPL           // tmpl
%token DCL_IMPL           // impl
%token DCL_EXTERN         // extern
%token DCL_NOTATION       // notation

%{ open Syntax0 %}

%start <dcl list> main

%%
// basics
let trivial :=
  | { () }

let iden ==
  | ~ = ID; <>

let const0 ==
  | ~ = CONST0; <>

let const1 ==
  | ~ = CONST1; <>

let at_iden ==
  | ~ = AT_ID; <>

let at_const0 ==
  | ~ = AT_CONSTANT0; <>

let at_const1 ==
  | ~ = AT_CONSTANT1; <>

// operators
let infix_op ==
  | ~ = OP_CAT; <>
  | ~ = OP_MUL; <>
  | ~ = OP_TIMES; <>
  | ~ = OP_OTIMES; <>
  | ~ = OP_DIV; <>
  | ~ = OP_REM; <>
  | ~ = OP_ADD; <>
  | ~ = OP_SUB; <>
  | LT; { "<" }
  | GT; { ">" }
  | ~ = OP_LT; <>
  | ~ = OP_GT; <>
  | ~ = OP_EQ; <>
  | ~ = OP_EX; <>
  | ~ = OP_AND; <>
  | ~ = OP_OR; <>
  | ~ = OP_COLON; <>
  | ~ = OP_AT; <>

let delim_op(P1,P2) ==
  | LPAREN; p1 = P1; COMMA; p2 = P2; RPAREN; { ("(,)", p1, p2) }
  | LBRACK; p1 = P1; COMMA; p2 = P2; RBRACK; { ("[,]", p1, p2) }
  | LANGLE; p1 = P1; COMMA; p2 = P2; RANGLE; { ("⟨,⟩", p1, p2) }
  | LBRACE; p1 = P1; COMMA; p2 = P2; RBRACE; { ("{,}", p1, p2) }
//
  | LPAREN; LBRACE; p1 = P1; RBRACE; COMMA; p2 = P2; RPAREN; { ("({},)", p1, p2) }
  | LPAREN; p1 = P1; COMMA; LBRACE; p2 = P2; RBRACE; RPAREN; { ("(,{})", p1, p2) }
//
  | LBRACK; LBRACE; p1 = P1; RBRACE; COMMA; p2 = P2; RBRACK; { ("[{},]", p1, p2) }
  | LBRACK; p1 = P1; COMMA; LBRACE; p2 = P2; RBRACE; RBRACK; { ("[,{}]", p1, p2) }
//
  | LANGLE; LBRACE; p1 = P1; RBRACE; COMMA; p2 = P2; RANGLE; { ("⟨{},⟩", p1, p2) }
  | LANGLE; p1 = P1; COMMA; LBRACE; p2 = P2; RBRACE; RANGLE; { ("⟨,{}⟩", p1, p2) }
//
  | LBRACE; LBRACE; p1 = P1; RBRACE; COMMA; p2 = P2; RBRACE; { ("{{},}", p1, p2) }
  | LBRACE; p1 = P1; COMMA; LBRACE; p2 = P2; RBRACE; RBRACE; { ("{,{}}", p1, p2) }

let weakfix_op ==
  | ~ = OP_SEMI; <>
  | SEMI; { ";" }

let prefix_op ==
  | ~ = OP_SIM; <>
  | ~ = OP_TIC; <>

// sorts
/* U L Type<s> */
let sort :=
  | SORT_U; { U }
  | SORT_L; { L }
  | id = iden; { SId id }

// identifiers
/* foo @foo foo[1,2,3] @foo[1,2,3] */
let tm_id :=
  | id = ID; { if id = "_" then IMeta else Id (id, I) }
  | id = AT_ID; { Id (id, E) }

// notation hole
/* %1 */
let tm_hole :=
  | i = HOLE; { Hole i }

// patterns
let tm_pattern0 :=
  | id = iden; { PId id }
  | TM_ABSURD; { PAbsurd }
  | LPAREN; id = iden; args = tm_pattern0s; RPAREN; { PConstr (id, args) }
  | p = delim_op(tm_pattern0i,tm_pattern0i); { let (s, p1, p2) = p in PBOpr (s, p1, p2) }
  | LPAREN; ~ = tm_pattern0i; RPAREN; <>

let tm_pattern0s :=
  | ~ = tm_pattern0+; <>

let tm_pattern0i :=
  | p1 = tm_pattern0i; s = infix_op; p2 = tm_pattern0i; { PBOpr (s, p1, p2) }
  | s = prefix_op; p = tm_pattern0i; { PUOpr (s, p) }
  | ~ = tm_pattern0; <>

let tm_pattern1 :=
  | id = iden; { PId id }
  | TM_ABSURD; { PAbsurd }
  | id = iden; ps = tm_pattern0s; { PConstr (id, ps) }
  | p = delim_op(tm_pattern1i,tm_pattern1i); { let (s, p1, p2) = p in PBOpr (s, p1, p2) }
  | LPAREN; ~ = tm_pattern1i; RPAREN; <>

let tm_pattern1i :=
  | p1 = tm_pattern1i; s = infix_op; p2 = tm_pattern1i; { PBOpr (s, p1, p2) }
  | s = prefix_op; p = tm_pattern1i; { PUOpr (s, p) }
  | ~ = tm_pattern1; <>

// clauses
let tm_cl0(P) :=
  | ps = separated_list(COMMA, tm_pattern1i); RIGHTARROW1; rhs = P?; { (ps, rhs) }

let tm_cl1(P) :=
  | PIPE; ps = separated_list(COMMA, tm_pattern1i); RIGHTARROW1; rhs = P?; { (ps, rhs) }

let tm_cls0 :=
  | cl = tm_cl1(tm); { [cl] }
  | cl = tm_cl1(tm_closed); cls = tm_cls0; { cl :: cls }

let tm_cls1 :=
  | cl = tm_cl0(tm); { [cl] }
  | cl = tm_cl0(tm_closed); cls = tm_cls0; { cl :: cls }
  | opt = option(tm_cls0);
    { match opt with Some cls -> cls | None -> [] }

// instance
/* X‹s,r,t› */
let tm_inst :=
  | id = const0; ss = separated_list(COMMA, sort); GT; { Inst (id, ss, I) }
  | id = const1; ss = separated_list(COMMA, sort); FRQ; { Inst (id, ss, I) }
  | id = at_const0; ss = separated_list(COMMA, sort); GT; { Inst (id, ss, E) }
  | id = at_const1; ss = separated_list(COMMA, sort); FRQ; { Inst (id, ss, E) }

// annotation
/* (m : A) */
let tm_ann :=
  | LPAREN; m = tm; COLON; a = tm; RPAREN; { Ann (m, a) }

let tm_ann_generic(P) :=
  | COLON; a = P; { Some a }
  | { None }

let tm_ann_closed :=
  | ~ = tm_ann_generic(tm_closed); <>

let tm_ann_open :=
  | ~ = tm_ann_generic(tm); <>

// sorts
/* U L Type‹s› */
let tm_type :=
  | SORT_U; { Type U }
  | SORT_L; { Type L }
  | TM_TYPE0; srt = sort; GT; { Type srt }
  | TM_TYPE1; srt = sort; FRQ; { Type srt }

// pi types
/*
∀ (x y z : A) -> B
∀ {x y z : A} -> B
∀ (x y z : A) -o B
∀ {x y z : A} -o B
forall<s>(x y z : A), B
forall<s>{x y z : A}, B
*/
let tm_pi_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids }

let tm_pi_args :=
  | args = tm_pi_arg+; { List.concat args }

let tm_pi(P) :=
  | FORALL; args = tm_pi_args; RIGHTARROW0; b = P;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_pi_args; MULTIMAP; b = P; 
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }
  | TM_FORALL0; s = sort; GT; args = tm_pi_args; COMMA; b = P;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, s, a, Binder (id, b))) args b }
  | TM_FORALL1; s = sort; FRQ; args = tm_pi_args; COMMA; b = P;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, s, a, Binder (id, b))) args b }

// lambda function
/*
fn x y z => m
fn (x y z : A) => m
fn {x y z : A} => m

ln x y z => m
ln (x y z : A) => m
ln {x y z : A} => m
*/
let tm_lam_arg :=
  | id = iden; { [ (R, id, IMeta) ] }
  | LPAREN; ids = iden+; RPAREN;
    { List.map (fun id -> (R, id, IMeta)) ids }
  | LBRACE; ids = iden+; RBRACE;
    { List.map (fun id -> (N, id, IMeta)) ids }
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids }

let tm_lam_args :=
  | args = tm_lam_arg+; { List.concat args }

let tm_lam(P) :=
  | TM_FN; args = tm_lam_args; opt = tm_ann_closed; RIGHTARROW1; m = P;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a = 
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Fun (a, Binder (None, [(ps, Some m)]), []) }
  | TM_LN; args = tm_lam_args; opt = tm_ann_closed; RIGHTARROW1; m = P;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a = 
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, L, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Fun (a, Binder (None, [(ps, Some m)]), []) }

// pattern fun
/*
fun 
| P => m

fun f
| P => m

fun : A -> B
| P => m

fun f : A -> B
| P => m
*/
let tm_fun_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids }

let tm_fun_args :=
  | args = tm_fun_arg*; { List.concat args }

let tm_fun :=
  | TM_FUN; id = iden?; args = tm_fun_args; opt = tm_ann_closed; cls = tm_cls0;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Fun (a, Binder (id, cls), []) }

// let expression
/*
let x := m in n
let x : A := m in n
let {x} := m in n
let {x} : A := m in n
*/
let tm_let(P) :=
  | TM_LET; p0 = tm_pattern1i; opt = tm_ann_open; ASSIGN; m = tm; TM_IN; n = P;
    { let m =
        match opt with
        | None -> m
        | Some a -> Ann (m, a)
      in
      Let (R, m, Binder (p0, n)) }
  | TM_LET; LBRACE; p0 = tm_pattern1i; RBRACE; opt = tm_ann_open; ASSIGN; m = tm; TM_IN; n = P;
    { let m =
        match opt with
        | None -> m
        | Some a -> Ann (m, a)
      in
      Let (N, m, Binder (p0, n)) }

// let clauses
/*
let fun f (x : A)
  | P => m
in n

let fun f (x : A) : A -> B
  | P => m
in n

let fun {f} (x : A)
  | P => m
in n

let fun {f} (x : A) : A -> B
  | P => m
in n
*/
let tm_letcls(P) :=
  | TM_LET; TM_FUN; id = iden; args = tm_fun_args; opt = tm_ann_closed;
    cls = tm_cls0; TM_IN; m = P;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Let (R, Fun (a, Binder (Some id, cls), []), Binder (PId id, m)) }
  | TM_LET; TM_FUN; LBRACE; id = iden; RBRACE; args = tm_fun_args; opt = tm_ann_closed;
    cls = tm_cls0; TM_IN; m = P;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Let (N, Fun (a, Binder (Some id, cls), []), Binder (PId id, m)) }

// let fun
/*
let fun f (x : A) := m
in n

let fun f (x : A) : B := m
in n

let fun {f} (x : A) := m
in n

let fun {f} (x : A) : B := m
in n
*/
let tm_letfun(P) :=
  | TM_LET; TM_FUN; id = iden; args = tm_fun_args; opt = tm_ann_open;
    ASSIGN; m = tm; TM_IN; n = P;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Let (R, Fun (a, Binder (Some id, [(ps, Some m)]), []), Binder (PId id, n)) }
  | TM_LET; TM_FUN; LBRACE; id = iden; RBRACE; args = tm_fun_args; opt = tm_ann_open;
    ASSIGN; m = tm; TM_IN; n = P;
    { let b =
        match opt with
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Let (N, Fun (a, Binder (Some id, [(ps, Some m)]), []), Binder (PId id, n)) }

// match expression
/*
match m, n with
| P1, P2 => rhs

match m as x, n as y in A x y with
| P1, P2 => rhs

match m as x : A, n as y : B x in A x y with
| P1, P2 => rhs

match {m} as x : A, {n} as y : B x in A x y with
| P1, P2 => rhs
*/
let tm_match_arg :=
  | m = tm; { (R, m, None) }
  | m = tm; TM_AS; id = iden; { (R, m, Some (id, IMeta)) }
  | m = tm; TM_AS; id = iden; COLON; a = tm; { (R, m, Some (id, a)) }
  | LBRACE; m = tm; RBRACE; { (N, m, None) }
  | LBRACE; m = tm; RBRACE; TM_AS; id = iden; { (N, m, Some (id, IMeta)) }
  | LBRACE; m = tm; RBRACE; TM_AS; id = iden; COLON; a = tm; { (N, m, Some (id, a)) }

let tm_match_args :=
  | ~ = separated_list(COMMA, tm_match_arg); <>

let tm_match :=
  | TM_MATCH; args = tm_match_args; TM_WITH; cls = tm_cls1;
    { Match (args, None, cls) }
  | TM_MATCH; args = tm_match_args; TM_IN; a = tm; TM_WITH; cls = tm_cls1;
    { Match (args, Some a, cls) }

// if-then-else expression
/*
if m then n1 else n2
*/
let tm_ifte(P) :=
  | TM_IF; m = tm; TM_THEN; n1 = tm; TM_ELSE; n2 = P;
    { Match ([(R, m, None)], None, [ ([PId "true"], Some n1); ([PId "false"], Some n2)]) }
  | TM_IF; LBRACE; m = tm; RBRACE; TM_THEN; n1 = tm; TM_ELSE; n2 = P;
    { Match ([(N, m, None)], None, [ ([PId "true"], Some n1); ([PId "false"], Some n2)]) }

// io
/* IO A */
let tm_io :=
  | TM_IO; a = tm1; { IO a }

// return
/* return m */
let tm_return :=
  | TM_RETURN; m = tm1; { Return m }

// mlet
/* let* x := m in n */
let tm_mlet(P) :=
  | TM_MLET; p0 = tm_pattern1i; opt = tm_ann_open; ASSIGN; m = tm; TM_IN; n = P;
    { let m =
        match opt with
        | None -> m
        | Some a -> Ann (m, IO a)
      in
      MLet (m, Binder (p0, n)) }

// primitive types
/* int char string */
let tm_prim_type :=
  | PRIM_INT_T; { Int_t }
  | PRIM_CHAR_T; { Char_t }
  | PRIM_STRING_T; { String_t }

// primitive terms
let tm_prim_term :=
  | i = PRIM_INT; { Int i }
  | c = PRIM_CHAR; { Char c }
  | s = PRIM_STRING; { String s }

// primitive operators
let tm_prim_opr :=
  | PRIM_NEG; m = tm1; { Neg m }
  | PRIM_ADD; m = tm1; n = tm1; { Add (m, n) }
  | PRIM_SUB; m = tm1; n = tm1; { Sub (m, n) }
  | PRIM_MUL; m = tm1; n = tm1; { Mul (m, n) }
  | PRIM_DIV; m = tm1; n = tm1; { Div (m, n) }
  | PRIM_REM; m = tm1; n = tm1; { Rem (m, n) }
  | PRIM_LTE; m = tm1; n = tm1; { Lte (m, n) }
  | PRIM_GTE; m = tm1; n = tm1; { Gte (m, n) }
  | PRIM_LT; m = tm1; n = tm1; { Lt (m, n) }
  | PRIM_GT; m = tm1; n = tm1; { Gt (m, n) }
  | PRIM_EQ; m = tm1; n = tm1; { Eq (m, n) }
  | PRIM_CHR; m = tm1; { Chr (m) }
  | PRIM_ORD; m = tm1; { Ord (m) }
  | PRIM_PUSH; m = tm1; n = tm1; { Push (m, n) }
  | PRIM_CAT; m = tm1; n = tm1; { Cat (m, n) }
  | PRIM_SIZE; m = tm1; { Size m }
  | PRIM_INDX; m = tm1; n = tm1; { Indx (m, n) }

// primitive sessions
let tm_prim_sess :=
  | PRIM_PROTO; { Proto }
  | PRIM_END; { End }
  | BULLET; { End }
  | PRIM_CH; a = tm; RANGLE; { Ch (true, a) }
  | PRIM_HC; a = tm; RANGLE; { Ch (false, a) }

// session actions
/*
⇑{x : A} → b
⇓(x : A) → b
*/
let tm_act_arg :=
  | LPAREN; id = iden; COLON; a = tm; RPAREN; { (R, id, a) } 
  | LBRACE; id = iden; COLON; a = tm; RBRACE; { (N, id, a) } 
  | LPAREN; a = tm; RPAREN; { (R, "_", a) } 
  | LBRACE; a = tm; RBRACE; { (N, "_", a) } 

let tm_act(P) :=
  | UPARROW1; arg = tm_act_arg; RIGHTARROW0; b = P;
    { let relv, id, a = arg in Act (relv, true, a, Binder (id, b)) }
  | DOWNARROW1; arg = tm_act_arg; RIGHTARROW0; b = P;
    { let relv, id, a = arg in Act (relv, false, a, Binder (id, b)) }

// primitive effects
let tm_prim_eff :=
  | PRIM_PRINT; m = tm1; { Print m }
  | PRIM_PRERR; m = tm1; { Prerr m }
  | PRIM_READLN; m = tm1; { ReadLn m }
  | PRIM_FORK; m = tm1; { Fork m }
  | PRIM_SEND; m = tm1; { Send m }
  | PRIM_RECV; m = tm1; { Recv m }
  | PRIM_CLOSE; m = tm1; { Close m }

// magic
/*
#magic
#magic[A]
*/
let tm_magic :=
  | TM_MAGIC0; { Magic IMeta }
  | TM_MAGIC1; a = tm; RBRACK; { Magic a }

// terms
let tm0 :=
  | ~ = tm_id; <>
  | ~ = tm_hole; <>
  | ~ = tm_ann; <>
  | ~ = tm_inst; <>
  | m = delim_op(tm,tm); { let (s, m1, m2) = m in BOpr (s, m1, m2) }
  | LPAREN; ~ = tm; RPAREN; <>
  | m = tm0; DLBRACK; ns = separated_list(RLBRACK,tm); RBRACK;
    { List.fold_left (fun acc n -> Indx (acc, n)) m ns }

let tm1 :=
  | ~ = tm_type; <>
  | ~ = tm_io; <>
  | ~ = tm_return; <>
  | ~ = tm_prim_type; <>
  | ~ = tm_prim_term; <>
  | ~ = tm_prim_opr; <>
  | ~ = tm_prim_sess; <>
  | ~ = tm_prim_eff; <>
  | ~ = tm_magic; <>
  | ~ = tm0; <>

let tm2 :=
  | ms = tm1+; { match ms with [ m ] -> m | _ -> App ms }

let tm3 :=
  | m = tm3; s = infix_op; n = tm3; { BOpr (s, m, n) }
  | s = prefix_op; m = tm3; { UOpr (s, m) }
  | ~ = tm2; <>

let tm4_generic(P) :=
  | a = tm3; RIGHTARROW0; b = tm4_generic(P); { Pi (R, U, a, Binder ("_", b)) }
  | a = tm3; MULTIMAP; b = tm4_generic(P); { Pi (R, L, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; RIGHTARROW0; b = tm4_generic(P); { Pi (N, U, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; MULTIMAP; b = tm4_generic(P); { Pi (N, L, a, Binder ("_", b)) }
  | ms = tm1*; m = tm_pi(P); { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_act(P); { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm3; <>

let tm5_generic(P) :=
  | ms = tm1*; m = tm_lam(P);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_let(P);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_letcls(P);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_letfun(P);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_mlet(P);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_ifte(P);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm4_generic(P); <>

let tm5_closed :=
  | m = tm3; s = weakfix_op; n = tm5_closed; { BOpr (s, m, n) }
  | ~ = tm5_generic(tm_closed); <>

let tm5 :=
  | ms = tm1*; m = tm_fun;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm1*; m = tm_match;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | m = tm3; s = weakfix_op; n = tm5; { BOpr (s, m, n) }
  | ~ = tm5_generic(tm); <>

let tm_closed :=
  | ~ = tm5_closed; <>

let tm :=
  | ~ = tm5; <>

// dcl modifier
let dcl_modifier :=
  | MODIFIER; MOD_PROGRAM; RBRACK; { R }
  | MODIFIER; MOD_LOGICAL; RBRACK; { N }
  | { R }

// dcl identifier
let dcl_iden :=
  | id = const0; sargs = separated_list(COMMA, iden); GT; { (id, sargs) }
  | id = const1; sargs = separated_list(COMMA, iden); FRQ; { (id, sargs) }
  | id = iden; { (id, []) }

// dcl arguments
let dcl_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a, E)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a, E)) ids }
  | QLPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a, I)) ids }
  | QLBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a, I)) ids }

let dcl_args :=
  | args = dcl_arg*; { List.concat args }

// def
/*
#[logical]
def foo‹s› (x : A) (y : B) : C := m

#[program]
def foo‹s› (x : A) : A -> B
  | P x => n
*/
let dcl_def :=
  | relv = dcl_modifier;
    DCL_DEF; id_sids = dcl_iden; args = dcl_args; COLON; b = tm_closed; cls = tm_cls0;
    { let id, sids = id_sids in
      let a, view =
        List.fold_right (fun (relv, id, a, v) (b, view) ->
          (Pi (relv, U, a, Binder (id, b)), v :: view)) args (b, [])
      in
      let ps = List.map (fun (_, id, _, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      let m = Fun (a, Binder (Some id, cls), view) in
      let sch = Binder (sids, (m, a)) in
      Definition { name = id; relv; body = sch; view } }
  | relv = dcl_modifier;
    DCL_DEF; id_sids = dcl_iden; args = dcl_args; opt = tm_ann_open; ASSIGN; m = tm;
    { let id, sids = id_sids in
      let b =
        match opt with
        | Some b -> b
        | None -> IMeta
      in
      let a, view =
        List.fold_right (fun (relv, id, a, v) (b, view) ->
          (Pi (relv, U, a, Binder (id, b)), v :: view)) args (b, [])
      in
      let m =
        match args with
        | [] -> m
        | _ ->
          let ps = List.map (fun (_, id, _, _) -> PId id) args in
          Fun (a, Binder (Some id, [(ps, Some m)]), view)
      in
      let sch = Binder (sids, (m, a)) in
      Definition { name = id; relv; body = sch; view } }

// inductive
/*
#[logical]
inductive vec‹s,r› (A : Type‹s›) : nat -> Type‹r› where
| vnil : vec<s,r>A zero
| #[multiplicative]
  vcons {n : nat} (hd : A) (tl : vec‹s,r›A n) : vec‹s,r›A (succ n)
*/
let dcl_ind_param :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (id, a, E)) ids }
  | QLPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (id, a, I)) ids }

let dcl_ind_params :=
  | args = dcl_ind_param*; { List.concat args }

let dcl_ind_tele :=
  | a = tm;
    { let rec aux = function
        | Pi (R, U, a, Binder (id, b)) ->
          TBind (R, a, Binder (id, aux b))
        | a -> TBase a
      in aux a }

let dcl_dconstr_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN; { List.map (fun id -> (R, id, a, E)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE; { List.map (fun id -> (N, id, a, E)) ids }
  | QLPAREN; ids = iden+; COLON; a = tm; RPAREN; { List.map (fun id -> (R, id, a, I)) ids }
  | QLBRACE; ids = iden+; COLON; a = tm; RBRACE; { List.map (fun id -> (N, id, a, I)) ids }

let dcl_dconstr_args :=
  | args = dcl_dconstr_arg*; { List.concat args }

let dcl_dconstr :=
  | PIPE; id = iden; args = dcl_dconstr_args; COLON; b = tm_closed;
    { let tele, view =
        List.fold_right (fun (relv, id, a, v) (tele, view) ->
          (TBind (relv, a, Binder (id, tele)), v :: view))
        args (TBase b, [])
      in
      DConstr (id, tele, view) }

let dcl_dconstrs :=
  | ~ = dcl_dconstr*; <>

let dcl_inductive :=
  | relv = dcl_modifier;
    DCL_INDUCTIVE; id_sids = dcl_iden; params = dcl_ind_params; COLON;
    tele = dcl_ind_tele; DCL_WHERE; dconstrs = dcl_dconstrs;
    { let id, sids = id_sids in
      let param, view = 
        List.fold_right (fun (id, a, v) (param, view) ->
          (PBind (a, Binder (id, param)), v :: view))
        params (PBase (tele, dconstrs), [])
      in
      let sch = Binder (sids, param) in
      Inductive { name = id; relv; body = sch; view } }

// external
/*
#[logical]
extern foo‹s› (x : A) (y : B) : C

#[program]
extern foo‹s› (x : A) : A -> B

#[program]
extern foo‹s› (x : A) : A -> B := m
*/
let dcl_extern :=
  | relv = dcl_modifier;
    DCL_EXTERN; id_sids = dcl_iden; args = dcl_args; COLON; b = tm;
    { let id, sids = id_sids in
      let a, view =
        List.fold_right (fun (relv, id, a, v) (b, view) ->
          (Pi (relv, U, a, Binder (id, b)), v :: view)) args (b, [])
      in
      let sch = Binder (sids, (None, a)) in
      Extern { name = id; relv; body = sch; view } }
  | relv = dcl_modifier;
    DCL_EXTERN; id_sids = dcl_iden; args = dcl_args; COLON; b = tm_closed; cls = tm_cls0;
    { let id, sids = id_sids in
      let a, view =
        List.fold_right (fun (relv, id, a, v) (b, view) ->
          (Pi (relv, U, a, Binder (id, b)), v :: view)) args (b, [])
      in
      let ps = List.map (fun (_, id, _, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      let m = Fun (a, Binder (Some id, cls), view) in
      let sch = Binder (sids, (Some m, a)) in
      Extern { name = id; relv; body = sch; view } }
  | relv = dcl_modifier;
    DCL_EXTERN; id_sids = dcl_iden; args = dcl_args; opt = tm_ann_open;
    ASSIGN; m = tm;
    { let id, sids = id_sids in
      let b =
        match opt with
        | Some b -> b
        | None -> IMeta
      in
      let a, view =
        List.fold_right (fun (relv, id, a, v) (b, view) ->
          (Pi (relv, U, a, Binder (id, b)), v :: view)) args (b, [])
      in
      let m =
        match args with
        | [] -> m
        | _ ->
          let ps = List.map (fun (_, id, _, _) -> PId id) args in
          Fun (a, Binder (Some id, [(ps, Some m)]), view)
      in
      let sch = Binder (sids, (Some m, a)) in
      Extern { name = id; relv; body = sch; view } }

// notations
/*
notation ( = ) := eq %1 %2
*/
let dcl_notation_symbol :=
  | ~ = infix_op; <>
  | ~ = prefix_op; <>
  | ~ = weakfix_op; <>
  | p = delim_op(trivial,trivial); { let (s, _, _) = p in s }

let dcl_notation :=
  | DCL_NOTATION; LPAREN; s = dcl_notation_symbol; RPAREN; ASSIGN; m = tm;
    { Notation { name = s; body = m } }

// declarations
let dcl :=
  | ~ = dcl_def; <>
  | ~ = dcl_inductive; <>
  | ~ = dcl_extern; <>
  | ~ = dcl_notation; <>

// main
let main :=
  | ~ = dcl*; EOF; <>
