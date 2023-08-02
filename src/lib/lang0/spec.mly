%token EOF

// delimiters
%token LPAREN // (
%token RPAREN // )
%token LBRACK // [
%token RBRACK // ]
%token LBRACE // {
%token RBRACE // {
%token LANGLE // ⟨
%token RANGLE // ⟩
%token FLQ    // ‹
%token FRQ    // ›

// quantifiers
%token FORALL // ∀
%token EXISTS // ∃

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

// products
%token TIMES  // ×
%token OTIMES // ⊗
%right TIMES
%right OTIMES

// unit
%token TOP
%token UNIT_TYPE // unit

// bool
%token BOOL_TYPE  // bool
%token BOOL_TRUE  // true
%token BOOL_FALSE // false
%token BOOL_AND   // &&
%token BOOL_OR    // ||
%left BOOL_AND
%left BOOL_OR

// nat
%token NAT_TYPE // nat
%token NAT_ZERO // O
%token NAT_SUCC // S
%token NAT_ADD  // +
%token NAT_SUB  // -
%token NAT_MUL  // *
%token NAT_DIV  // /
%token NAT_MOD  // %
%token NAT_LTE  // <=
%token NAT_GTE  // >=
%token NAT_LT   // <
%token NAT_GT   // >
%token NAT_EQ   // ==
%token NAT_NEQ  // !=
%left NAT_ADD
%left NAT_SUB
%left NAT_MUL
%left NAT_DIV
%left NAT_MOD
%left NAT_LTE
%left NAT_GTE
%left NAT_LT
%left NAT_GT
%left NAT_EQ
%left NAT_NEQ

// string
%token<int> CHAR
%token<int list> STRING
%token STR_CAT // ^
%left STR_CAT

// list
%token LIST_CONS // ::
%right LIST_CONS

// bottom
%token BOT // ⊥

// equality
%token EQUAL  // =
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
%token SORT_L // U

// prim
%token PRIM_STDIN  // stdin
%token PRIM_STDOUT // stdout
%token PRIM_STDERR // stderr

// identifier
%token<int> INTEGER
%token<string> IDENTIFIER

// tm
%token TM_TYPE     // Type
%token TM_FORALL   // forall
%token TM_FN       // fn
%token TM_LN       // fn
%token TM_FUNCTION // function
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
%token TM_ABSURD   // absurd
%token TM_MAGIC    // #magic
%token TM_REW      // rew
%token TM_IO       // IO
%token TM_RETURN   // return
%token TM_MLET     // let*
%token TM_PROTO    // proto
%token TM_END      // end
%token TM_CH       // ch⟨
%token TM_HC       // hc⟨
%token TM_OPEN     // open
%token TM_FORK     // fork
%token TM_RECV     // recv
%token TM_SEND     // send
%token TM_CLOSE    // close
%token TM_SLEEP    // sleep
%token TM_RAND     // rand

// modifiers
%token MOD_PROGRAM        // program
%token MOD_LOGICAL        // logical
%token MOD_MULTIPLICATIVE // multiplicative
%token MOD_ADDITIVE       // additive
%token MODIFIER           // #[

// dcl
%token DCL_DEF            // def
%token DCL_INDUCTIVE      // inductive
%token DCL_WHERE          // where

%{ open Syntax %}

%start <tm> main

%%

let iden ==
  | ~ = IDENTIFIER; <>

let sort :=
  | SORT_U; { U }
  | SORT_L; { L }
  | id = iden; { SId id }

let tm_id :=
  | id = iden; { Id id }

// instance
let tm_inst :=
  | id = iden; FLQ; ss = separated_list(COMMA, sort); FRQ;
    { Inst (id, ss) }

// annotation
let tm_ann :=
  | LPAREN; m = tm; COLON; a = tm; RPAREN; { Ann (m, a) }

// sorts
let tm_type :=
  | SORT_U; { Type U }
  | SORT_L; { Type L }
  | TM_TYPE; FLQ; id = iden; FRQ; { Type (SId id) }

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

let tm_pi_closed :=
  | FORALL; args = tm_pi_args; RIGHTARROW0; b = tm_closed;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_pi_args; MULTIMAP; b = tm_closed; 
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }
  | TM_FORALL;
    FLQ; s = sort; FRQ; args = tm_pi_args; COMMA; b = tm_closed;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, s, a, Binder (id, b))) args b }

let tm_pi :=
  | FORALL; args = tm_pi_args; RIGHTARROW0; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_pi_args; MULTIMAP; b = tm; 
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }
  | TM_FORALL;
    FLQ; s = sort; FRQ; args = tm_pi_args; COMMA; b = tm;
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
  | id = iden; { [ (R, id, Id "_") ] }
  | LPAREN; ids = iden+; RPAREN;
    { List.map (fun id -> (R, id, Id "_")) ids }
  | LBRACE; ids = iden+; RBRACE;
    { List.map (fun id -> (N, id, Id "_")) ids }
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids }

let tm_lam_args :=
  | args = tm_lam_arg+; { List.concat args }

let tm_lam_closed :=
  | TM_FN; args = tm_lam_args; RIGHTARROW1; m = tm_closed;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, U, a, Binder (id, m))) args m }
  | TM_LN; args = tm_lam_args; RIGHTARROW1; m = tm_closed;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, L, a, Binder (id, m))) args m }

let tm_lam :=
  | TM_FN; args = tm_lam_args; RIGHTARROW1; m = tm;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, U, a, Binder (id, m))) args m }
  | TM_LN; args = tm_lam_args; RIGHTARROW1; m = tm;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, L, a, Binder (id, m))) args m }

// pattern function
/*
function 
| P => m

function f
| P => m

function : A -> B
| P => m

function f : A -> B
| P => m
*/
let tm_fun_p :=
  | id = iden; { PId id }
  | LPAREN; id = iden; args = tm_fun_ps; RPAREN;
    { PMul (id, args) }
  | LPAREN; id = iden; DOT; i = INTEGER;  args = tm_fun_ps; RPAREN;
    { PAdd (id, i, args) }
  | LPAREN; ~ = tm_fun_p; RPAREN; <>

let tm_fun_ps :=
  | ~ = tm_fun_p+; <>

let tm_fun_closed :=
  | PIPE; ps = tm_fun_ps; RIGHTARROW1; rhs = tm_closed; { (ps, rhs) }

let tm_fun_open :=
  | PIPE; ps = tm_fun_ps; RIGHTARROW1; rhs = tm; { (ps, rhs) }

let tm_fun_cls :=
  | cl = tm_fun_open; { [cl] }
  | cl = tm_fun_closed; cls = tm_fun_cls; { cl :: cls }

let tm_fun :=
  | TM_FUNCTION; cls = tm_fun_cls;
    { Fun (None, Binder (None, cls)) }
  | TM_FUNCTION; id = iden; cls = tm_fun_cls;
    { Fun (None, Binder (Some id, cls)) }
  | TM_FUNCTION; COLON; a = tm_closed; cls = tm_fun_cls;
    { Fun (Some a, Binder (None, cls)) }
  | TM_FUNCTION; id = iden; COLON; a = tm_closed; cls = tm_fun_cls;
    { Fun (Some a, Binder (Some id, cls)) }

// let expression
/*
let x := m in n
let x : A := m in n
let {x} := m in n
let {x} : A := m in n
*/
let tm_let_closed :=
  | TM_LET; id = iden; ASSIGN; m = tm; TM_IN; n = tm_closed;
    { Let (R, m, Binder (id, n)) }
  | TM_LET; id = iden; COLON; a = tm; ASSIGN; m = tm; TM_IN; n = tm_closed;
    { Let (R, Ann (m, a), Binder (id, n)) }
  | TM_LET; LBRACE; id = iden; RBRACE; ASSIGN; m = tm; TM_IN; n = tm_closed;
    { Let (N, m, Binder (id, n)) }
  | TM_LET; LBRACE; id = iden; COLON; a = tm; RBRACE; ASSIGN; m = tm; TM_IN; n = tm_closed;
    { Let (N, Ann (m, a), Binder (id, n)) }

let tm_let :=
  | TM_LET; id = iden; ASSIGN; m = tm; TM_IN; n = tm;
    { Let (R, m, Binder (id, n)) }
  | TM_LET; id = iden; COLON; a = tm; ASSIGN; m = tm; TM_IN; n = tm;
    { Let (R, Ann (m, a), Binder (id, n)) }
  | TM_LET; LBRACE; id = iden; RBRACE; ASSIGN; m = tm; TM_IN; n = tm;
    { Let (N, m, Binder (id, n)) }
  | TM_LET; LBRACE; id = iden; RBRACE; COLON; a = tm; ASSIGN; m = tm; TM_IN; n = tm;
    { Let (N, Ann (m, a), Binder (id, n)) }

// let function
/*
let function f
  | P => m
in n

let function f : A -> B
  | P => m
in n

let function {f}
  | P => m
in n

let function {f} : A -> B
  | P => m
in n
*/
let tm_letfun_closed :=
  | TM_LET; TM_FUNCTION; id = iden; cls = tm_fun_cls; TM_IN; m = tm_closed;
    { Let (R, Fun (None, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; id = iden; COLON; a = tm_closed; cls = tm_fun_cls; TM_IN; m = tm_closed;
    { Let (R, Fun (Some a, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; cls = tm_fun_cls; TM_IN; m = tm_closed;
    { Let (N, Fun (None, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; COLON; a = tm_closed; cls = tm_fun_cls; TM_IN; m = tm_closed;
    { Let (N, Fun (Some a, Binder (Some id, cls)), Binder (id, m)) }

let tm_letfun :=
  | TM_LET; TM_FUNCTION; id = iden; cls = tm_fun_cls; TM_IN; m = tm;
    { Let (R, Fun (None, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; id = iden; COLON; a = tm_closed; cls = tm_fun_cls; TM_IN; m = tm;
    { Let (R, Fun (Some a, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; cls = tm_fun_cls; TM_IN; m = tm;
    { Let (N, Fun (None, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; COLON; a = tm_closed; cls = tm_fun_cls; TM_IN; m = tm;
    { Let (N, Fun (Some a, Binder (Some id, cls)), Binder (id, m)) }


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
  | m = tm; TM_AS; id = iden; { (R, m, Some (id, Id "_")) }
  | m = tm; TM_AS; id = iden; COLON; a = tm; { (R, m, Some (id, a)) }
  | LBRACE; m = tm; RBRACE; { (N, m, None) }
  | LBRACE; m = tm; RBRACE; TM_AS; id = iden; { (N, m, Some (id, Id "_")) }
  | LBRACE; m = tm; RBRACE; TM_AS; id = iden; COLON; a = tm; { (N, m, Some (id, a)) }

let tm_match_args :=
  | ~ = separated_list(COMMA, tm_match_arg); <>

let tm_match_p0 :=
  | id = iden; { PId id }
  | LPAREN; id = iden; args = tm_match_p0s; RPAREN;
    { PMul (id, args) }
  | LPAREN; id = iden; DOT; i = INTEGER;  args = tm_match_p0s; RPAREN;
    { PAdd (id, i, args) }
  | LPAREN; ~ = tm_match_p0; RPAREN; <>

let tm_match_p0s :=
  | ~ = tm_fun_p+; <>

let tm_match_p :=
  | id = iden; { PId id }
  | id = iden; ps = tm_match_p0s; { PMul (id, ps) }
  | id = iden; DOT; i = INTEGER; ps = tm_match_p0s; { PAdd (id, i, ps) }
  | LPAREN; ~ = tm_match_p; RPAREN; <>

let tm_match_closed :=
  | PIPE; ps = separated_list(COMMA, tm_match_p); RIGHTARROW1; rhs = tm_closed; { (ps, rhs) }

let tm_match_open :=
  | PIPE; ps = separated_list(COMMA, tm_match_p); RIGHTARROW1; rhs = tm; { (ps, rhs) }

let tm_match_cl0 :=
  | ps = separated_list(COMMA, tm_match_p); RIGHTARROW1; rhs = tm; { (ps, rhs) }

let tm_match_cl0_closed :=
  | ps = separated_list(COMMA, tm_match_p); RIGHTARROW1; rhs = tm_closed; { (ps, rhs) }

let tm_match_cls0 :=
  | cl = tm_match_open; { [cl] }
  | cl = tm_match_closed; cls = tm_match_cls0; { cl :: cls }

let tm_match_cls :=
  | cl = tm_match_cl0; { [cl] }
  | cl = tm_match_cl0_closed; cls = tm_match_cls0; { cl :: cls }
  | opt = option(tm_match_cls0);
    { match opt with
      | Some cls -> cls
      | None -> [] }

let tm_match :=
  | TM_MATCH; args = tm_match_args; TM_WITH; cls = tm_match_cls;
    { Match (args, None, cls) }
  | TM_MATCH; args = tm_match_args; TM_IN; a = tm; TM_WITH; cls = tm_match_cls;
    { Match (args, Some a, cls) }

// io
/* IO A */
let tm_io :=
  | TM_IO; a = tm0; { IO a }

// return
/* return m */
let tm_return :=
  | TM_RETURN; m = tm0; { Return m }

// mlet
/* let x <- m in n */
let tm_mlet_closed :=
  | TM_MLET; id = iden; ASSIGN; m = tm; TM_IN; n = tm_closed;
    { MLet (m, Binder (id, n)) }
  | TM_MLET; id = iden; COLON; a = tm; ASSIGN; m = tm; TM_IN; n = tm_closed;
    { MLet (Ann (m, a), Binder (id, n)) }

let tm_mlet :=
  | TM_MLET; id = iden; ASSIGN; m = tm; TM_IN; n = tm;
    { MLet (m, Binder (id, n)) }
  | TM_MLET; id = iden; COLON; a = tm; ASSIGN; m = tm; TM_IN; n = tm;
    { MLet (Ann (m, a), Binder (id, n)) }

// absurd
/* #absurd */
let tm_absurd :=
  | TM_ABSURD; { Absurd }

// magic
/*
#magic
#magic[A]
*/
let tm_magic :=
  | TM_MAGIC; { Magic (Id "_") }
  | TM_MAGIC; LBRACK; a = tm; RBRACK; { Magic a }

// terms
let tm0 :=
  | ~ = tm_ann; <>
  | ~ = tm_inst; <>
  | ~ = tm_id; <>
  | ~ = tm_type; <>
  | ~ = tm_absurd; <>
  | ~ = tm_io; <>
  | ~ = tm_return; <>
  | ~ = tm_magic; <>
  | LPAREN; ~ = tm; RPAREN; <>

let tm1 :=
  | m = tm0; ms = tm0*;
    { match ms with [] -> m | _ -> App (m :: ms) }

let tm2 :=
  | a = tm2; RIGHTARROW0; b = tm2; { Pi (R, U, a, Binder ("_", b)) }
  | a = tm2; MULTIMAP; b = tm2; { Pi (R, L, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; RIGHTARROW0; b = tm2; { Pi (N, U, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; MULTIMAP; b = tm2; { Pi (N, L, a, Binder ("_", b)) }
  | ~ = tm1; <>

let tm3_closed :=
  | ms = tm0*; m = tm_pi_closed;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_lam_closed;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_let_closed;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_letfun_closed;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_mlet_closed;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm2; <>

let tm3 :=
  | ms = tm0*; m = tm_pi;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_lam;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  (* end-clause *)
  | ms = tm0*; m = tm_fun;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_let;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_letfun;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  (* end-clause *)
  | ms = tm0*; m = tm_match;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_mlet;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm2; <>

let tm_closed :=
  | ~ = tm3_closed; <>

let tm :=
  | ~ = tm3; <>

let main :=
  | ~ = tm; EOF; <>
