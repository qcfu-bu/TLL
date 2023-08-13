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
%token FLQ     // ‹
%token FRQ     // ›
%token QLPAREN // ?(
%token QLBRACE // ?{

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

// products
%token TIMES  // ×
%token OTIMES // ⊗
%token AT     // @
%right TIMES
%right OTIMES

// unit
%token TOP

// bool
%token AND   // &&
%token OR    // ||
%left AND
%left OR

// nat
%token ADD  // +
%token SUB  // -
%token MUL  // *
%token DIV  // /
%token REM  // %
%token LTE  // <=
%token GTE  // >=
%token LT   // <
%token GT   // >
%token EQEQ // ==
%token NEQ  // !=
%left ADD
%left SUB
%left MUL
%left DIV
%left MOD
%left LTE
%left GTE
%left LT
%left GT
%left EQEQ
%left NEQ

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
%token<int> INTEGER          // 123
%token<string> IDENTIFIER    // foo
%token<string> CONSTANT0     // foo<
%token<string> CONSTANT1     // foo‹
%token<string> AT_IDENTIFIER // @foo
%token<string> AT_CONSTANT0  // @foo<
%token<string> AT_CONSTANT1  // @foo‹

// tm
%token TM_TYPE0    // Type<
%token TM_TYPE1    // Type‹
%token TM_FORALL0  // forall<
%token TM_FORALL1  // forall‹
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

%{ open Syntax0 %}

%start <dcl list> main

%%
// baiscs
let iden ==
  | ~ = IDENTIFIER; <>

let const0 ==
  | ~ = CONSTANT0; <>

let const1 ==
  | ~ = CONSTANT1; <>

let at_iden ==
  | ~ = AT_IDENTIFIER; <>

let at_const0 ==
  | ~ = AT_CONSTANT0; <>

let at_const1 ==
  | ~ = AT_CONSTANT1; <>

// sorts
/* U L Type<s> */
let sort :=
  | SORT_U; { U }
  | SORT_L; { L }
  | id = iden; { SId id }

// identifiers
/* foo @foo */
let tm_id :=
  | id = iden; { if id = "_" then IMeta else Id (id, I) }
  | id = at_iden; { Id (id, E) }

// instance
/* X‹s,r,t› */
let tm_inst :=
  | id = const0; ss = separated_list(COMMA, sort); GT;
    { Inst (id, ss, I) }
  | id = const1; ss = separated_list(COMMA, sort); FRQ;
    { Inst (id, ss, I) }
  | id = at_const0; ss = separated_list(COMMA, sort); GT;
    { Inst (id, ss, E) }
  | id = at_const1; ss = separated_list(COMMA, sort); FRQ;
    { Inst (id, ss, E) }

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

let tm_pi(p) :=
  | FORALL; args = tm_pi_args; RIGHTARROW0; b = p;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_pi_args; MULTIMAP; b = p; 
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }
  | TM_FORALL0; s = sort; GT; args = tm_pi_args; COMMA; b = p;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, s, a, Binder (id, b))) args b }
  | TM_FORALL1; s = sort; FRQ; args = tm_pi_args; COMMA; b = p;
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

let tm_lam(p) :=
  | TM_FN; args = tm_lam_args; opt = tm_ann_closed; RIGHTARROW1; m = p;
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
  | TM_LN; args = tm_lam_args; opt = tm_ann_closed; RIGHTARROW1; m = p;
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
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      let cls = List.map (fun (ps0, rhs) -> (ps @ ps0, rhs)) cls in
      Let (R, Fun (a, Binder (Some id, cls), []), Binder (id, m)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; args = tm_fun_args; opt = tm_ann_closed;
    cls = tm_fun_cls; TM_IN; m = p;
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
      Let (N, Fun (a, Binder (Some id, cls), []), Binder (id, m)) }

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
        | None -> IMeta
        | Some b -> b
      in
      let a =
        List.fold_right (fun (relv, id, a) acc ->
          Pi (relv, U, a, Binder (id, acc))) args b
      in
      let ps = List.map (fun (_, id, _) -> PId id) args in
      Let (R, Fun (a, Binder (Some id, [(ps, Some m)]), []), Binder (id, n)) }
  | TM_LET; TM_FUNCTION; LBRACE; id = iden; RBRACE; args = tm_fun_args; opt = tm_ann_open;
    ASSIGN; m = tm; TM_IN; n = p;
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
      Let (N, Fun (a, Binder (Some id, [(ps, Some m)]), []), Binder (id, n)) }

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
        | Some a -> Ann (m, IO a)
      in
      MLet (m, Binder (id, n)) }

// magic
/*
#magic
#magic[A]
*/
let tm_magic :=
  | TM_MAGIC; { Magic IMeta }
  | TM_MAGIC; LBRACK; a = tm; RBRACK; { Magic a }

// terms
let tm0 :=
  | ~ = tm_ann; <>
  | ~ = tm_type; <>
  | ~ = tm_io; <>
  | ~ = tm_return; <>
  | ~ = tm_magic; <>
  | ~ = tm_id; <>
  | ~ = tm_inst; <>
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

// dcl identifier
let dcl_iden :=
  | id = const0; sargs = separated_list(COMMA, iden); GT; { (id, sargs) }
  | id = const1; sargs = separated_list(COMMA, iden); FRQ; { (id, sargs) }
  | id = iden; { (id, []) }

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
    { List.map (fun id -> (R, id, a, E)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a, E)) ids }
  | QLPAREN; ids = iden+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a, I)) ids }
  | QLBRACE; ids = iden+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a, I)) ids }

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
    DCL_DEF; id_sids = dcl_iden; args = dcl_def_args; COLON; b = tm_closed;
    cls = dcl_def_cls;
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
    DCL_DEF; id_sids = dcl_iden; args = dcl_def_args; opt = tm_ann_open;
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

let dcl_dconstr_modifier :=
  | MODIFIER; MOD_MULTIPLICATIVE; RBRACK; { fun id tele view -> DMul (id, tele, view) }
  | MODIFIER; MOD_ADDITIVE; RBRACK; { fun id tele view -> DAdd (id, tele, view) }
  | { fun id tele view -> DMul (id, tele, view) }

let dcl_dconstr_arg :=
  | LPAREN; ids = iden+; COLON; a = tm; RPAREN; { List.map (fun id -> (R, id, a, E)) ids }
  | LBRACE; ids = iden+; COLON; a = tm; RBRACE; { List.map (fun id -> (N, id, a, E)) ids }
  | QLPAREN; ids = iden+; COLON; a = tm; RPAREN; { List.map (fun id -> (R, id, a, I)) ids }
  | QLBRACE; ids = iden+; COLON; a = tm; RBRACE; { List.map (fun id -> (N, id, a, I)) ids }

let dcl_dconstr_args :=
  | args = dcl_dconstr_arg*; { List.concat args }

let dcl_dconstr :=
  | PIPE; modifier = dcl_dconstr_modifier;
    id = iden; args = dcl_dconstr_args; COLON; b = tm_closed;
    { let tele, view =
        List.fold_right (fun (relv, id, a, v) (tele, view) ->
          (TBind (relv, a, Binder (id, tele)), v :: view))
        args (TBase b, [])
      in
      modifier id tele view }

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

// declarations
let dcl :=
  | ~ = dcl_def; <>
  | ~ = dcl_inductive; <>

// main
let main :=
  | ~ = dcl*; EOF; <>
