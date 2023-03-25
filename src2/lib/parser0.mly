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
%left ARITH_ADD
%left ARITH_SUB
%left ARITH_MUL
%left ARITH_DIV
%left ARITH_MOD
%left ARITH_LTE
%left ARITH_GTE
%left ARITH_LT
%left ARITH_GT
%left ARITH_EQ
%left ARITH_NEQ

// boolean
%token BOOL_AND // &&
%token BOOL_OR  // ||
%left BOOL_AND
%left BOOL_OR

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
%left SEMI

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
%token TM_MATCH  // match
%token TM_WITH   // with
%token TM_REFL   // refl
%token TM_REW    // rew
%token TM_IO     // IO
%token TM_RETURN // return
%token TM_PROTO  // proto
%token TM_END    // end
%token TM_CH     // ch⟨
%token TM_HC     // hc⟨
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

let tm_ann :=
  | LPAREN; m = tm; COLON; a = tm; RPAREN; { Ann (m, a) }

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

let tm_arg1 :=
  | LPAREN; ids = nonempty_list(identifier); COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids } 
  | LBRACE; ids = nonempty_list(identifier); COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids } 

let tm_arg2 :=
  | LPAREN; id = identifier; COLON; a = tm; RPAREN; { (R, id, a) } 
  | LBRACE; id = identifier; COLON; a = tm; RBRACE; { (N, id, a) } 
  | LPAREN; a = tm; RPAREN; { (R, "_", a) } 
  | LBRACE; a = tm; RBRACE; { (N, "_", a) } 

let tm_args0 :=
  | args = nonempty_list(tm_arg0); { List.concat args }

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
    { MLet (m, Binder (id, n)) }
  | TM_LET; id = identifier; COLON; a = tm; LEFTARROW1; m = tm; TM_IN; n = tm;
    { MLet (Ann (m, IO a), Binder (id, n)) }

let tm_proto :=
  | TM_PROTO; { Proto }

let tm_end :=
  | BULLET; { End }

let tm_act :=
  | UPARROW1; arg = tm_arg2; RIGHTARROW0; b = tm;
    { let rel, id, a = arg in
      Act (rel, Pos, a, Binder (id, b)) }
  | DOWNARROW1; arg = tm_arg2; RIGHTARROW0; b = tm;
    { let rel, id, a = arg in
      Act (rel, Neg, a, Binder (id, b)) }

let tm_ch :=
  | TM_CH; a = tm; RANGLE; { Ch (Pos, a) }
  | TM_HC; a = tm; RANGLE; { Ch (Neg, a) }

let tm_open :=
  | TM_OPEN; PRIM_STDIN; { Open Stdin }
  | TM_OPEN; PRIM_STDOUT; { Open Stdout }
  | TM_OPEN; PRIM_STDERR; { Open Stderr }

let tm_fork :=
  | TM_FORK; LPAREN;
      id = identifier; COLON; a = tm;
    RPAREN; TM_IN; m = tm;
    { Fork (a, Binder(id, m)) }

let tm_recv :=
  | TM_RECV; m = tm0; { Recv m }

let tm_send :=
  | TM_SEND; m = tm0; { Send m }

let tm_close :=
  | TM_CLOSE; m = tm0; { Close m }

let tm0 :=
  | ~ = id; <>
  | ~ = tm_ann; <>
  | ~ = tm_type; <>
  | ~ = tm_pair; <>
  | ~ = tm_match; <>
  | ~ = tm_refl; <>
  | ~ = tm_proto; <>
  | ~ = tm_end; <>
  | ~ = tm_ch; <>
  | ~ = tm_open; <>
  | LPAREN; ~ = tm; RPAREN; <>

let tm1 :=
  | ~ = tm_io; <>
  | ~ = tm_return; <>
  | ~ = tm_recv; <>
  | ~ = tm_send; <>
  | ~ = tm_close; <>
  | m = tm0; ms = list(tm0);
    { match ms with [] -> m | _ -> App (m :: ms) }

let tm2 :=
  | m = tm2; ARITH_MUL; n = tm2; { App [Id "muln"; m; n] }
  | m = tm2; ARITH_DIV; n = tm2; { App [Id "divn"; m; n] }
  | m = tm2; ARITH_MOD; n = tm2; { App [Id "modn"; m; n] }
  | m = tm2; ARITH_ADD; n = tm2; { App [Id "addn"; m; n] }
  | m = tm2; ARITH_SUB; n = tm2; { App [Id "subn"; m; n] }
  | m = tm2; ARITH_LTE; n = tm2; { App [Id "lten"; m; n]}
  | m = tm2; ARITH_GTE; n = tm2; { App [Id "gten"; m; n]}
  | m = tm2; ARITH_LT; n = tm2; { App [Id "ltn"; m; n]}
  | m = tm2; ARITH_GT; n = tm2; { App [Id "gtn"; m; n]}
  | m = tm2; ARITH_EQ; n = tm2; { App [Id "eqn"; m; n]}
  | m = tm2; ARITH_NEQ; n = tm2; { App [Id "neqn"; m; n]}
  | m = tm2; BOOL_AND; n = tm2; { App [Id "andb"; m; n] }
  | m = tm2; BOOL_OR; n = tm2; { App [Id "orb"; m; n] }
  | m = tm2; SEMI; n = tm2; { MLet (m, Binder ("_", n)) }
  | ~ = tm1; <>

let tm3 :=
  | ARITH_SUB; m = tm2; { App [Id "negn"; m] }
  | ~ = tm2; <>

let tm4 :=
  | m = tm4; EQUIV; n = tm4;
    { Eq (m, n) }
  | a = tm4; TIMES; b = tm4;
    { Sigma (R, U, a, Binder ("_", b)) }
  | a = tm4; OTIMES; b = tm4;
    { Sigma (R, L, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; TIMES; b = tm4;
    { Sigma (N, U, a, Binder ("_", b)) }
  | LBRACE; a = tm; RBRACE; OTIMES; b = tm4;
    { Sigma (N, L, a, Binder ("_", b)) }
  | a = tm4; RIGHTARROW0; b = tm4;
    { Pi (R, U, a, Binder ("_", b))}
  | a = tm4; MULTIMAP; b = tm4;
    { Pi (R, L, a, Binder ("_", b))}
  | LBRACE; a = tm; RBRACE; RIGHTARROW0; b = tm4;
    { Pi (N, U, a, Binder ("_", b))}
  | LBRACE; a = tm; RBRACE; MULTIMAP; b = tm4;
    { Pi (N, L, a, Binder ("_", b))}
  | ~ = tm3; <>

let tm5 :=
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
  | ms = list(tm0); m = tm_act;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = list(tm0); m = tm_fork;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm4; <>

let tm6 :=
  | NEGATE; m = tm5; { App [Id "negate"; m] }
  | ~ = tm5; <>

let tm := 
  | ~ = tm6; <>

let main :=
  | ~ = tm; EOF; <>
