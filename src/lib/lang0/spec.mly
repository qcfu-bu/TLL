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

// bool
%token BOOL_AND   // &&
%token BOOL_OR    // ||
%left BOOL_AND
%left BOOL_OR

// nat
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
%token SORT_L // L

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
%token TM_ABSURD   // !!
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

%start <dcl list> main

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
/* X‹s,r,t› */
let tm_inst :=
  | id = iden; FLQ; ss = separated_list(COMMA, sort); FRQ;
    { Inst (id, ss) }

// annotation
/* (m : A) */
let tm_ann :=
  | LPAREN; m = tm; COLON; a = tm; RPAREN; { Ann (m, a) }

let tm_ann_generic(p) :=
  | COLON; a = p; { Some a }
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
  | TM_TYPE; FLQ; srt = sort; FRQ; { Type srt }

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

let tm_pi(p) :=
  | FORALL; args = tm_pi_args; RIGHTARROW0; b = p;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_pi_args; MULTIMAP; b = p; 
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }
  | TM_FORALL;
    FLQ; s = sort; FRQ; args = tm_pi_args; COMMA; b = p;
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

let tm_lam(p) :=
  | TM_FN; args = tm_lam_args; opt = tm_ann_closed; RIGHTARROW1; m = p;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a = 
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Fun (a, Binder (None, [(ps, Some m)])) }
  | TM_LN; args = tm_lam_args; opt = tm_ann_closed; RIGHTARROW1; m = p;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a = 
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, L, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Fun (a, Binder (None, [(ps, Some m)])) }

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
let tm_fun_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids }

let tm_fun_args :=
  | args = tm_fun_arg*; { List.concat args }

let tm_fun_p :=
  | id = iden; { PId id }
  | TM_ABSURD; { PAbsurd }
  | LPAREN; id = iden; args = tm_fun_ps; RPAREN;
    { PMul (id, args) }
  | LPAREN; id = iden; DOT; i = INTEGER;  args = tm_fun_ps; RPAREN;
    { PAdd (id, i, args) }
  | LPAREN; ~ = tm_fun_p; RPAREN; <>

let tm_fun_ps :=
  | ~ = tm_fun_p+; <>

let tm_fun_cl(p) :=
  | PIPE; ps = tm_fun_ps; RIGHTARROW1; rhs = p?; { (ps, rhs) }

let tm_fun_cls :=
  | cl = tm_fun_cl(tm); { [cl] }
  | cl = tm_fun_cl(tm_closed); cls = tm_fun_cls; { cl :: cls }

let tm_fun :=
  | TM_FUNCTION; id = iden?; args = tm_fun_args; opt = tm_ann_closed; cls = tm_fun_cls;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Fun (a, Binder (id, cls)) }

// let expression
/*
let x := m in n
let x : A := m in n
let {x} := m in n
let {x} : A := m in n
*/
let tm_let(p) :=
  | TM_LET; id = iden; opt = tm_ann_open; ASSIGN; m = tm; TM_IN; n = p;
    { let m =
        match opt with
        | None -> m
        | Some a -> Ann (m, a)
      in
      Let (R, m, Binder (id, n)) }
  | TM_LET; LBRACE; id = iden; RBRACE; opt = tm_ann_open; ASSIGN; m = tm; TM_IN; n = p;
    { let m =
        match opt with
        | None -> m
        | Some a -> Ann (m, a)
      in
      Let (N, m, Binder (id, n)) }

// let clauses
/*
let function f (x : A)
  | P => m
in n

let function f (x : A) : A -> B
  | P => m
in n

let function {f} (x : A)
  | P => m
in n

let function {f} (x : A) : A -> B
  | P => m
in n
*/
let tm_letcls(p) :=
  | TM_LET; TM_FUNCTION; id = iden; args = tm_fun_args; opt = tm_ann_closed;
    cls = tm_fun_cls; TM_IN; m = p;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Let (R, Fun (a, Binder (Some id, cls)), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; args = tm_fun_args; opt = tm_ann_closed;
    cls = tm_fun_cls; TM_IN; m = p;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Let (N, Fun (a, Binder (Some id, cls)), Binder (id, m)) }

// let function
/*
let function f (x : A) := m
in n

let function f (x : A) : B := m
in n

let function {f} (x : A) := m
in n

let function {f} (x : A) : B := m
in n
*/
let tm_letfun(p) :=
  | TM_LET; TM_FUNCTION; id = iden; args = tm_fun_args; opt = tm_ann_open;
    ASSIGN; m = tm; TM_IN; n = p;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Let (R, Fun (a, Binder (Some id, [(ps, Some m)])), Binder (id, n)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; args = tm_fun_args; opt = tm_ann_open;
    ASSIGN; m = tm; TM_IN; n = p;
    { let b =
        match opt with
        | None -> Id "_"
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Let (N, Fun (a, Binder (Some id, [(ps, Some m)])), Binder (id, n)) }

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
  | TM_ABSURD; { PAbsurd }
  | LPAREN; id = iden; args = tm_match_p0s; RPAREN;
    { PMul (id, args) }
  | LPAREN; id = iden; DOT; i = INTEGER;  args = tm_match_p0s; RPAREN;
    { PAdd (id, i, args) }
  | LPAREN; ~ = tm_match_p0; RPAREN; <>

let tm_match_p0s :=
  | ~ = tm_match_p0+; <>

let tm_match_p :=
  | id = iden; { PId id }
  | TM_ABSURD; { PAbsurd }
  | id = iden; ps = tm_match_p0s; { PMul (id, ps) }
  | id = iden; DOT; i = INTEGER; ps = tm_match_p0s; { PAdd (id, i, ps) }
  | LPAREN; ~ = tm_match_p; RPAREN; <>

let tm_match_cl0(p) :=
  | ps = separated_list(COMMA, tm_match_p); RIGHTARROW1; rhs = p?; { (ps, rhs) }

let tm_match_cl1(p) :=
  | PIPE; ps = separated_list(COMMA, tm_match_p); RIGHTARROW1; rhs = p?; { (ps, rhs) }

let tm_match_cls0 :=
  | cl = tm_match_cl1(tm); { [cl] }
  | cl = tm_match_cl1(tm_closed); cls = tm_match_cls0; { cl :: cls }

let tm_match_cls :=
  | cl = tm_match_cl0(tm); { [cl] }
  | cl = tm_match_cl0(tm_closed); cls = tm_match_cls0; { cl :: cls }
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
/* let* x := m in n */
let tm_mlet(p) :=
  | TM_MLET; id = iden; opt = tm_ann_open; ASSIGN; m = tm; TM_IN; n = p;
    { let m =
        match opt with
        | None -> m
        | Some a -> Ann (m, a)
      in
      MLet (m, Binder (id, n)) }

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

let tm3_generic(p) :=
  | ms = tm0*; m = tm_pi(p);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_lam(p);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_let(p);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_letcls(p);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_letfun(p);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_mlet(p);
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm2; <>

let tm3_closed :=
  | ~ = tm3_generic(tm_closed); <>

let tm3 :=
  | ms = tm0*; m = tm_fun;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_match;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm3_generic(tm); <>

let tm_closed :=
  | ~ = tm3_closed; <>

let tm :=
  | ~ = tm3; <>

// dcl modifier
let dcl_modifier :=
  | MODIFIER; MOD_PROGRAM; RBRACK; { R }
  | MODIFIER; MOD_LOGICAL; RBRACK; { N }
  | { R }

// dcl sort args
let dcl_sargs :=
  | FLQ; ~ = separated_list(COMMA, iden); FRQ; <>
  | { [] }

// def
/*
#[logical]
def foo‹s› (x : A) (y : B) : C := m

#[program]
def foo‹s› (x : A) : A -> B
  | P x => n
*/
let dcl_def_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids }

let dcl_def_args :=
  | args = dcl_def_arg*; { List.concat args }

let dcl_def_p :=
  | id = iden; { PId id }
  | TM_ABSURD; { PAbsurd }
  | LPAREN; id = iden; args = dcl_def_ps; RPAREN;
    { PMul (id, args) }
  | LPAREN; id = iden; DOT; i = INTEGER;  args = dcl_def_ps; RPAREN;
    { PAdd (id, i, args) }
  | LPAREN; ~ = dcl_def_p; RPAREN; <>

let dcl_def_ps :=
  | ~ = dcl_def_p+; <>

let dcl_def_closed :=
  | PIPE; ps = dcl_def_ps; RIGHTARROW1; rhs = tm_closed?; { (ps, rhs) }

let dcl_def_open :=
  | PIPE; ps = dcl_def_ps; RIGHTARROW1; rhs = tm?; { (ps, rhs) }

let dcl_def_cls :=
  | cl = dcl_def_open; { [cl] }
  | cl = dcl_def_closed; cls = dcl_def_cls; { cl :: cls }

let dcl_def :=
  | relv = dcl_modifier;
    DCL_DEF; id = iden; sids = dcl_sargs; args = dcl_def_args; COLON; b = tm_closed;
    cls = dcl_def_cls;
    { let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      let m = Fun (a, Binder (Some id, cls)) in
      let sch = Binder (sids, (m, a)) in
      Definition { name = id; relv = relv; body = sch } }
  | relv = dcl_modifier;
    DCL_DEF; id = iden; sids = dcl_sargs; args = dcl_def_args; COLON; b = tm;
    ASSIGN; m = tm;
    { let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let m =
        match args with
        | [] -> m
        | _ ->
          let ps = List.map (fun (_, id, _) -> PId id) args in
          Fun (a, Binder (Some id, [(ps, Some m)]))
      in
      let sch = Binder (sids, (m, a)) in
      Definition { name = id; relv = relv; body = sch } }

// inductive
/*
#[logical]
inductive vec‹s,r› (A : Type‹s›) : nat -> Type‹r› where
| vnil : vec<s,r>A zero
| #[multiplicative]
  vcons {n : nat} (hd : A) (tl : vec‹s,r›A n) : vec‹s,r›A (succ n)
*/
let dcl_ind_param :=
  | LPAREN; id = iden; COLON; a = tm; RPAREN; { (id, a) }

let dcl_ind_params :=
  | ~ = dcl_ind_param*; <>

let dcl_ind_tele :=
  | a = tm;
    { let rec aux = function
        | Pi (R, U, a, Binder (id, b)) ->
          TBind (R, a, Binder (id, aux b))
        | a -> TBase a
      in aux a }

let dcl_dconstr_modifier :=
  | MODIFIER; MOD_MULTIPLICATIVE; RBRACK; { fun id tele -> DMul (id, tele) }
  | MODIFIER; MOD_ADDITIVE; RBRACK; { fun id tele -> DAdd (id, tele) }
  | { fun id tele -> DMul (id, tele) }

let dcl_dconstr_arg :=
  | LPAREN; id = iden; COLON; a = tm; RPAREN; { (R, id, a) }
  | LBRACE; id = iden; COLON; a = tm; RBRACE; { (N, id, a) }

let dcl_dconstr_args :=
  | ~ = dcl_dconstr_arg*; <>

let dcl_dconstr :=
  | PIPE; modifier = dcl_dconstr_modifier;
    id = iden; args = dcl_dconstr_args; COLON; b = tm_closed;
    { let tele =
        List.fold_right (fun (relv, id, a) acc ->
          TBind (relv, a, Binder (id, acc))) args (TBase b)
      in
      modifier id tele }

let dcl_dconstrs :=
  | ~ = dcl_dconstr*; <>

let dcl_inductive :=
  | relv = dcl_modifier;
    DCL_INDUCTIVE; id = iden; sids = dcl_sargs; params = dcl_ind_params; COLON;
    tele = dcl_ind_tele; DCL_WHERE; dconstrs = dcl_dconstrs;
    { let params = 
        List.fold_right (fun (id, a) acc ->
          PBind (a, Binder (id, acc))) params (PBase (tele, dconstrs))
      in
      let sch = Binder (sids, params) in
      Inductive { name = id; relv = relv; body = sch } }

// declarations
let dcl :=
  | ~ = dcl_def; <>
  | ~ = dcl_inductive; <>

// main
let main :=
  | ~ = dcl*; EOF; <>
