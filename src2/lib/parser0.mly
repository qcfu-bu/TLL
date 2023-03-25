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
%token POS    // !
%token NEG    // ?

// arrows
%token LEFTARROW0  // ←
%token LEFTARROW1  // ⇐
%token RIGHTARROW0 // →
%token RIGHTARROW1 // ⇒
%token MULTIMAP    // ⊸
%right RIGHTARROW0
%right MULTIMAP

// products
%token TIMES  // ×
%token OTIMES // ⊗
%right TIMES
%right OTIMES

// arithmetic
%token ARITH_ADD  // +
%token ARITH_SUB  // -
%token ARITH_MUL  // *
%token ARITH_DIV  // /
%token ARITH_MOD  // %
%token ARITH_LTE  // <=
%token ARITH_GTE  // >=
%token ARITH_LT   // <
%token ARITH_GT   // <
%token ARITH_EQ   // ==
%token ARITH_NEQ  // !=

// boolean
%token BOOL_AND // &&
%token BOOL_OR  // ||

// equality
%token EQUAL  // =
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

// sort
%token SORT_U // U
%token SORT_L // U

// prim
%token PRIM_STDIN  // stdin
%token PRIM_STDOUT // stdout
%token PRIM_STDERR // stderr

// identifier
%token<string> IDENTIFIER

// tm
%token TM_FN     // fn
%token TM_LN     // fn
%token TM_LET    // let
%token TM_IN     // in
%token TM_FIX    // fix
%token TM_MATCH  // match
%token TM_WITH   // with
%token TM_REFL   // refl
%token TM_REW    // rew
%token TM_IO     // IO
%token TM_RETURN // return
%token TM_PROTO  // proto
%token TM_END    // end
%token TM_CH     // ch‹
%token TM_HC     // hc‹
%token TM_OPEN   // open
%token TM_FORK   // fork
%token TM_RECV   // recv
%token TM_SEND   // send
%token TM_CLOSE  // close

// dcl
%token DCL_DEFINITION // definition
%token DCL_THEOREM    // theorem
%token DCL_INDUCTIVE  // inductive

// dcons
%token DCONS_OF // of


%{ open Syntax0 %}

%start <tm> main

%%

let identifier :=
  | ~ = IDENTIFIER; <>

let id :=
  | id = identifier; { Id id }

let tm_type :=
  | SORT_U; { Type U }
  | SORT_L; { Type L }

let tm_arg0 :=
  | id = identifier;
    { [(R, id, None)] }
  | LPAREN; ids = nonempty_list(identifier); RPAREN;
    { List.map (fun id -> (R, id, None)) ids }
  | LBRACE; ids = nonempty_list(identifier); RBRACE;
    { List.map (fun id -> (N, id, None)) ids }
  | LPAREN; ids = nonempty_list(identifier); COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, Some a)) ids } 
  | LBRACE; ids = nonempty_list(identifier); COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, Some a)) ids } 

let tm_args0 :=
  | args = nonempty_list(tm_arg0); { List.concat args }

let tm_arg1 :=
  | LPAREN; ids = nonempty_list(identifier); COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids } 
  | LBRACE; ids = nonempty_list(identifier); COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids } 

let tm_args1 :=
  | args = nonempty_list(tm_arg1); { List.concat args }

let tm_pi :=
  | FORALL; args = tm_args1; RIGHTARROW0; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_args1; MULTIMAP; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }

let tm_lam :=
  | TM_FN; args = tm_args0; RIGHTARROW1; m = tm;
    { let m, a =
        List.fold_right (fun (rel, id, opt) (m, b) ->
            match opt with
            | Some a ->
              (Lam (rel, U, Binder (id, m)),
               Pi  (rel, U, a, Binder (id, b)))
            | None ->
              (Lam (rel, U, Binder (id, m)),
               Pi  (rel, U, Id "_", Binder (id, b))))
        args (m, Id "_")
      in Ann (m, a) }
  | TM_LN; args = tm_args0; RIGHTARROW1; m = tm;
    { let m, a =
        List.fold_right (fun (rel, id, opt) (m, b) ->
            match opt with
            | Some a ->
              (Lam (rel, L, Binder (id, m)),
               Pi  (rel, L, a, Binder (id, b)))
            | None ->
              (Lam (rel, L, Binder (id, m)),
               Pi  (rel, L, Id "_", Binder (id, b))))
        args (m, Id "_")
      in Ann (m, a) }

let tm_let :=
  | TM_LET; id = identifier; EQUAL; m = tm; TM_IN; n = tm;
    { Let (R, m, Binder (id, n)) }
  | TM_LET; id = identifier; COLON; a = tm; EQUAL; m = tm; TM_IN; n = tm;
    { Let (R, Ann (m, a), Binder (id, n)) }
  | TM_LET; LBRACE; id = identifier; RBRACE; EQUAL; m = tm; TM_IN; n = tm;
    { Let (N, m, Binder (id, n)) }
  | TM_LET; LBRACE; id = identifier; COLON; a = tm; RBRACE; EQUAL; m = tm; TM_IN; n = tm;
    { Let (N, Ann (m, a), Binder (id, n)) }

let tm_sigma :=
  | EXISTS; args = tm_args1; TIMES; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Sigma (rel, U, a, Binder (id, b))) args b }
  | EXISTS; args = tm_args1; OTIMES; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Sigma (rel, L, a, Binder (id, b))) args b }

let tm_pair :=
  | LPAREN; m = tm; COMMA; n = tm; RPAREN;
    { Pair (R, U, m, n) }
  | LANGLE; m = tm; COMMA; n = tm; RANGLE;
    { Pair (R, L, m, n) }
  | LPAREN; LBRACE; m = tm; RBRACE; COMMA; n = tm; RPAREN;
    { Pair (N, U, m, n) }
  | LANGLE; LBRACE; m = tm; RBRACE; COMMA; n = tm; RANGLE;
    { Pair (N, L, m, n) }

let tm_match :=
  | TM_MATCH; m = tm;
    TM_WITH; cls = tm_cls; TM_END;
    { Match (m, Binder ("_", Id "_"), cls) }
  | TM_MATCH; m = tm;
    LBRACK; id = identifier; RIGHTARROW1; a = tm; RBRACK;
    TM_WITH; cls = tm_cls; TM_END;
    { Match (m, Binder (id, a), cls) }

let tm_cl0 :=
  | LPAREN; LBRACE; id1 = identifier; RBRACE; id2 = identifier; RPAREN;
    RIGHTARROW1; m = tm;
    { PPair (N, U, MBinder ([id1; id2], m)) }
  | LANGLE; LBRACE; id1 = identifier; RBRACE; id2 = identifier; RANGLE;
    RIGHTARROW1; m = tm;
    { PPair (N, L, MBinder ([id1; id2], m)) }
  | LPAREN; id1 = identifier; id2 = identifier; RPAREN;
    RIGHTARROW1; m = tm;
    { PPair (R, U, MBinder ([id1; id2], m)) }
  | LANGLE; id1 = identifier; id2 = identifier; RANGLE;
    RIGHTARROW1; m = tm;
    { PPair (R, L, MBinder ([id1; id2], m)) }

let tm_cl1 :=
  | PIPE; ~ = tm_cl0; <>

let tm_cls :=
  | cl0 = tm_cl0; cls = list(tm_cl1); { cl0 :: cls }
  | ~ = list(tm_cl1); <>

let tm_refl :=
  | TM_REFL; { Refl }

let tm_rew :=
  | TM_REW; LBRACK;
      id1 = identifier; COMMA; id2 = identifier; RIGHTARROW1; a = tm;
    RBRACK; p = tm; TM_IN; m = tm;
    { Rew (MBinder ([id1; id2], a), p, m) }

let tm_io :=
  | TM_IO; a = tm0; { IO a }

let tm_return :=
  | TM_RETURN; m = tm0; { Return m }

let tm_mlet :=
  | TM_LET; id = identifier; LEFTARROW1 ; m = tm; TM_IN; n = tm;
    { Let (R, m, Binder (id, n)) }
  | TM_LET; id = identifier; COLON; a = tm; LEFTARROW1; m = tm; TM_IN; n = tm;
    { Let (R, Ann (m, IO a), Binder (id, n)) }

let tm_end :=
  | BULLET; { End }

let tm0 :=
  | ~ = id; <>
  | ~ = tm_type; <>
  | ~ = tm_pair; <>
  | ~ = tm_match; <>
  | ~ = tm_refl; <>
  | ~ = tm_end; <>
  | LPAREN; ~ = tm; RPAREN; <>

let tm1 :=
  | ~ = tm_io; <>
  | ~ = tm_return; <>
  | m = tm0; ms = list(tm0);
    { match ms with [] -> m | _ -> App (m :: ms) }

let tm2 :=
  | m = tm2; EQUIV; n = tm2;
    { Eq (m, n) }
  | a = tm2; TIMES; b = tm2;
    { Sigma (R, U, a, Binder ("_", b)) }
  | a = tm2; OTIMES; b = tm2;
    { Sigma (R, L, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; TIMES; b = tm2;
    { Sigma (N, U, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; OTIMES; b = tm2;
    { Sigma (N, L, a, Binder ("_", b)) }
  | a = tm2; RIGHTARROW0; b = tm2;
    { Pi (R, U, a, Binder ("_", b))}
  | a = tm2; MULTIMAP; b = tm2;
    { Pi (R, L, a, Binder ("_", b))}
  | LBRACE; a = tm; RBRACE; RIGHTARROW0; b = tm2;
    { Pi (N, U, a, Binder ("_", b))}
  | LBRACE; a = tm; RBRACE; MULTIMAP; b = tm2;
    { Pi (N, L, a, Binder ("_", b))}
  | ~ = tm1; <>

let tm3 :=
  | ms = list(tm0); a = tm_pi;
    { match ms with [] -> a | _ -> App (ms @ [a]) }
  | ms = list(tm0); m = tm_lam;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = list(tm0); m = tm_let;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = list(tm0); m = tm_sigma;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = list(tm0); m = tm_rew;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = list(tm0); m = tm_mlet;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm2; <>

let tm :=
  | ~ = tm3; <>

let main :=
  | ~ = tm; EOF; <>
