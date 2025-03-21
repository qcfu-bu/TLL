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

// arithmetic
%token ARITH_ADD  // +
%token ARITH_SUB  // -
%token ARITH_MUL  // *
%token ARITH_DIV  // /
%token ARITH_MOD  // %
%token ARITH_LTE  // <=
%token ARITH_GTE  // >=
%token ARITH_LT   // <
%token ARITH_GT   // >
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

// string
%token<bool list> ASCII
%token<bool list list> STRING
%token STR_CAT // ^
%left STR_CAT

// list
%token LIST_CONS // ::
%right LIST_CONS

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
%token TM_REW      // rew
%token TM_IO       // IO
%token TM_RETURN   // return
%token TM_PROTO    // proto
%token TM_END      // end
%token TM_CH       // ch⟨
%token TM_HC       // hc⟨
%token TM_OPEN     // open
%token TM_FORK     // fork
%token TM_RECV     // recv
%token TM_SEND     // send
%token TM_CLOSE    // close

// dcl
%token DCL_PROGRAM   // program
%token DCL_LOGICAL   // logical
%token DCL_INDUCTIVE // inductive

// dcons
%token DCONS_OF // of


%{ open Util
   open Syntax0 %}

%start <dcls> main

%%

let identifier ==
  | ~ = IDENTIFIER; <>

let sort :=
  | SORT_U; { U }
  | SORT_L; { L }
  | id = identifier; { SId id }

let tm_id :=
  | id = identifier; { Id id }

let tm_inst :=
  | id = identifier; FLQ; ss = separated_list(COMMA, sort); FRQ;
    { Inst (id, ss) }

let tm_unit :=
  | LPAREN; RPAREN; { Id "tt" }

let tm_nat :=
  | n = INTEGER;
    { let rec loop acc = function
        | n when n <= 0 -> acc
        | n -> loop (App [Id "S"; acc]) (n - 1) 
      in loop (Id "O") n }

let tm_ascii :=
  | ls = ASCII;
    { let ms = List.map (function
        | true -> Id "true"
        | false -> Id "false") ls
      in App (Id "Ascii" :: ms) }

let tm_string :=
  | lss = STRING;
    { let ms = List.map (fun ls ->
        let ms = List.map (function
          | true -> Id "true"
          | false -> Id "false") ls
        in App (Id "Ascii" :: ms)) lss
      in
      List.fold_right (fun m acc ->
        App [Id "String"; m; acc])
      ms (Id "EmptyString") }

let tm_ann :=
  | LPAREN; m = tm; COLON; a = tm; RPAREN; { Ann (m, a) }

let tm_type :=
  | SORT_U; { Type U }
  | SORT_L; { Type L }
  | TM_TYPE; FLQ; id = identifier; FRQ; { Type (SId id) }

let tm_arg0 :=
  | id = identifier;
    { [(R, id, Id "_")] }
  | LPAREN; ids = identifier+; RPAREN;
    { List.map (fun id -> (R, id, Id "_")) ids }
  | LBRACE; ids = identifier+; RBRACE;
    { List.map (fun id -> (N, id, Id "_")) ids }
  | LPAREN; ids = identifier+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids } 
  | LBRACE; ids = identifier+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids } 

let tm_arg1 :=
  | LPAREN; ids = identifier+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids } 
  | LBRACE; ids = identifier+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids } 

let tm_arg2 :=
  | LPAREN; id = identifier; COLON; a = tm; RPAREN; { (R, id, a) } 
  | LBRACE; id = identifier; COLON; a = tm; RBRACE; { (N, id, a) } 
  | LPAREN; a = tm; RPAREN; { (R, "_", a) } 
  | LBRACE; a = tm; RBRACE; { (N, "_", a) } 

let tm_args0 :=
  | args = tm_arg0+; { List.concat args }

let tm_args1 :=
  | args = tm_arg1+; { List.concat args }

let tm_pi :=
  | FORALL; args = tm_args1; RIGHTARROW0; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, U, a, Binder (id, b))) args b }
  | FORALL; args = tm_args1; MULTIMAP; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, L, a, Binder (id, b))) args b }
  | TM_FORALL;
    FLQ; s = sort; FRQ; args = tm_args1; COMMA; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Pi (rel, s, a, Binder (id, b))) args b }

let tm_lam :=
  | TM_FN; args = tm_args0; RIGHTARROW1; m = tm;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, U, a, Binder (id, m))) args m }
  | TM_LN; args = tm_args0; RIGHTARROW1; m = tm;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, L, a, Binder (id, m))) args m }
  | TM_FUNCTION;
    FLQ; s = sort; FRQ; args = tm_args0; COMMA; m = tm;
    { List.fold_right (fun (rel, id, a) m ->
        Lam (rel, s, a, Binder (id, m))) args m }

let tm_p0 :=
  | LPAREN; LBRACE;
      id1 = identifier; RBRACE; COMMA; id2 = identifier;
    RPAREN;
    { PPair (N, U, id1, id2) }
  | LANGLE; LBRACE;
      id1 = identifier; RBRACE; COMMA; id2 = identifier;
    RANGLE;
    { PPair (N, L, id1, id2) }
  | LPAREN; id1 = identifier; COMMA; id2 = identifier; RPAREN;
    { PPair (R, U, id1, id2) }
  | LANGLE; id1 = identifier; COMMA; id2 = identifier; RANGLE;
    { PPair (R, L, id1, id2) }
  | TM_TUP; FLQ; s = sort; FRQ;
    LPAREN; id1 = identifier; COMMA; id2 = identifier; RPAREN;
    { PPair (R, s, id1, id2) }
  | TM_TUP; FLQ; s = sort; FRQ;
    LPAREN; LBRACE;
      id1 = identifier; RBRACE; COMMA; id2 = identifier;
    RPAREN;
    { PPair (N, s, id1, id2) }

let tm_opt ==
  | id = identifier; { Left id }
  | p = tm_p0; { Right p }

let tm_let :=
  | TM_LET; opt = tm_opt; EQUAL; m = tm; TM_IN; n = tm;
    { Let (R, m, Binder (opt, n)) }
  | TM_LET; opt = tm_opt; COLON; a = tm; EQUAL; m = tm; TM_IN; n = tm;
    { Let (R, Ann (m, a), Binder (opt, n)) }
  | TM_LET; LBRACE; id = identifier; RBRACE; EQUAL; m = tm; TM_IN; n = tm;
    { Let (N, m, Binder (Left id, n)) }
  | TM_LET; LBRACE; id = identifier; COLON; a = tm; RBRACE; EQUAL; m = tm; TM_IN; n = tm;
    { Let (N, Ann (m, a), Binder (Left id, n)) }

let tm_sigma :=
  | EXISTS; args = tm_args1; TIMES; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Sigma (rel, U, a, Binder (id, b))) args b }
  | EXISTS; args = tm_args1; OTIMES; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Sigma (rel, L, a, Binder (id, b))) args b }
  | TM_EXISTS;
    FLQ; s = sort; FRQ; args = tm_args1; COMMA; b = tm;
    { List.fold_right (fun (rel, id, a) b ->
        Sigma (rel, s, a, Binder (id, b))) args b }

let tm_pair :=
  | LPAREN; m = tm; COMMA; n = tm; RPAREN;
    { Pair (R, U, m, n) }
  | LANGLE; m = tm; COMMA; n = tm; RANGLE;
    { Pair (R, L, m, n) }
  | LPAREN; LBRACE; m = tm; RBRACE; COMMA; n = tm; RPAREN;
    { Pair (N, U, m, n) }
  | LANGLE; LBRACE; m = tm; RBRACE; COMMA; n = tm; RANGLE;
    { Pair (N, L, m, n) }
  | TM_TUP; FLQ; s = sort; FRQ;
    LPAREN; m = tm; COMMA; n = tm; RPAREN;
    { Pair (R, s, m, n) }
  | TM_TUP; FLQ; s = sort; FRQ;
    LPAREN; LBRACE; m = tm; RBRACE; COMMA; n = tm; RPAREN;
    { Pair (N, s, m, n) }

let tm_match :=
  | TM_MATCH; m = tm; TM_WITH; cls = tm_cls; TM_END;
    { Match (m, Binder ("_", Id "_"), cls) }
  | TM_MATCH; m = tm;
      TM_AS ; id = identifier; TM_IN; a = tm;
    TM_WITH; cls = tm_cls; TM_END;
    { Match (m, Binder (id, a), cls) }

let tm_ifte :=
  | TM_IF; m = tm; TM_THEN; n1 = tm; TM_ELSE; n2 = tm;
    { Match (m, Binder ("_", Id "_"),
        [Binder (PCons ("true",  []), n1);
         Binder (PCons ("false", []), n2)]) }

let tm_p :=
  | ~ = tm_p0; <>
  | id1 = identifier; LIST_CONS; id2 = identifier;
    { PCons ("cons", [id1; id2]) }
  | id = identifier; ids = identifier*;
    { PCons (id, ids) }

let tm_cl0 :=
  | p = tm_p; RIGHTARROW1; m = tm; { Binder (p, m) }

let tm_cl1 :=
  | PIPE; ~ = tm_cl0; <>

let tm_cls :=
  | cl0 = tm_cl0; cls = tm_cl1*; { cl0 :: cls }
  | ~ = tm_cl1*; <>

let tm_refl :=
  | TM_REFL; { Refl }

let tm_rew :=
  | TM_REW; LBRACK;
      id1 = identifier; COMMA; id2 = identifier; RIGHTARROW1; a = tm;
    RBRACK; p = tm; TM_IN; m = tm;
    { Rew (Binder ((id1, id2), a), p, m) }

let tm_io :=
  | TM_IO; a = tm0; { IO a }

let tm_return :=
  | TM_RETURN; m = tm0; { Return m }

let tm_mlet :=
  | TM_LET; opt = tm_opt; LEFTARROW1 ; m = tm; TM_IN; n = tm;
    { MLet (m, Binder (opt, n)) }
  | TM_LET; opt = tm_opt; COLON; a = tm; LEFTARROW1; m = tm; TM_IN; n = tm;
    { MLet (Ann (m, IO a), Binder (opt, n)) }

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
  | ~ = tm_inst; <>
  | ~ = tm_id; <>
  | ~ = tm_unit; <>
  | ~ = tm_nat; <>
  | ~ = tm_ascii; <>
  | ~ = tm_string; <>
  | ~ = tm_ann; <>
  | ~ = tm_type; <>
  | ~ = tm_pair; <>
  | ~ = tm_match; <>
  | ~ = tm_refl; <>
  | ~ = tm_io; <>
  | ~ = tm_return; <>
  | ~ = tm_proto; <>
  | ~ = tm_end; <>
  | ~ = tm_ch; <>
  | ~ = tm_open; <>
  | ~ = tm_send; <>
  | ~ = tm_recv; <>
  | ~ = tm_close; <>
  | LPAREN; ~ = tm; RPAREN; <>

let tm1 :=
  | m = tm0; ms = tm0*;
    { match ms with [] -> m | _ -> App (m :: ms) }

let tm2 :=
  | m = tm2; ARITH_MUL;  n = tm2; { App [Id "muln"; m; n] }
  | m = tm2; ARITH_DIV;  n = tm2; { App [Id "divn"; m; n] }
  | m = tm2; ARITH_MOD;  n = tm2; { App [Id "modn"; m; n] }
  | m = tm2; ARITH_ADD;  n = tm2; { App [Id "addn"; m; n] }
  | m = tm2; ARITH_SUB;  n = tm2; { App [Id "subn"; m; n] }
  | m = tm2; ARITH_LTE;  n = tm2; { App [Id "lten"; m; n] }
  | m = tm2; ARITH_GTE;  n = tm2; { App [Id "gten"; m; n] }
  | m = tm2; ARITH_LT;   n = tm2; { App [Id "ltn"; m; n] }
  | m = tm2; ARITH_GT;   n = tm2; { App [Id "gtn"; m; n] }
  | m = tm2; ARITH_EQ;   n = tm2; { App [Id "eqn"; m; n] }
  | m = tm2; ARITH_NEQ;  n = tm2; { App [Id "neqn"; m; n] }
  | m = tm2; BOOL_AND;   n = tm2; { App [Id "andb"; m; n] }
  | m = tm2; BOOL_OR;    n = tm2; { App [Id "orb"; m; n] }
  | m = tm2; STR_CAT;    n = tm2; { App [Id "cats"; m; n] }
  | m = tm2; LIST_CONS; n = tm2; { App [Id "cons"; m; n] }
  | m = tm2; SEMI;       n = tm2; { MLet (m, Binder (Left "_", n)) }
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
  | ms = tm0*; a = tm_pi;
    { match ms with [] -> a | _ -> App (ms @ [a]) }
  | ms = tm0*; m = tm_lam;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_let;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_sigma;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_ifte;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_rew;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_mlet;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_act;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ms = tm0*; m = tm_fork;
    { match ms with [] -> m | _ -> App (ms @ [m]) }
  | ~ = tm4; <>

let tm6 :=
  | NEGATE; m = tm5; { App [Id "negate"; m] }
  | ~ = tm5; <>

let tm := 
  | ~ = tm6; <>

let dcl_arg0 :=
  | id = identifier;
    { [(R, id, None)] }
  | LPAREN; ids = identifier+; RPAREN;
    { List.map (fun id -> (R, id, None)) ids }
  | LBRACE; ids = identifier+; RBRACE;
    { List.map (fun id -> (N, id, None)) ids }
  | LPAREN; ids = identifier+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, Some a)) ids } 
  | LBRACE; ids = identifier+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, Some a)) ids } 

let dcl_arg1 :=
  | LPAREN; ids = identifier+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (id, a)) ids } 

let dcl_arg2 :=
  | LPAREN; ids = identifier+; COLON; a = tm; RPAREN;
    { List.map (fun id -> (R, id, a)) ids } 
  | LBRACE; ids = identifier+; COLON; a = tm; RBRACE;
    { List.map (fun id -> (N, id, a)) ids } 

let dcl_args0 :=
  | args = dcl_arg0*; { List.concat args }

let dcl_args1 :=
  | args = dcl_arg1*; { List.concat args }

let dcl_args2 :=
  | args = dcl_arg2*; { List.concat args }

let dcl_args :=
  | args = dcl_args0; COLON; a = tm; EQUAL; m = tm;
    { List.fold_right (fun (rel, id, opt) acc ->
        match opt with
        | Some a -> ABind (rel, a, Binder (id, acc))
        | None -> ABind (rel, Id "_", Binder (id, acc)))
      args (ABase (a, m)) }

let dcl_sargs :=
  | FLQ; ~ = separated_list(COMMA, identifier); FRQ; <>
  | { [] }

let dcl_dtm :=
  | DCL_PROGRAM; id = identifier; sids = dcl_sargs; args = dcl_args;
    { DTm (R, id, Binder (sids, args)) }
  | DCL_LOGICAL; id = identifier; sids = dcl_sargs; args = dcl_args;
    { DTm (N, id, Binder (sids, args)) }

let dcl_ptm :=
  | args = dcl_args1; COLON; b = tm; { (args, b) }

let dcl_dcons0 :=
  | id = identifier; { (id, []) }
  | id = identifier; DCONS_OF; args = dcl_args2; { (id, args) }

let dcl_dcons1 :=
  | PIPE; ~ = dcl_dcons0; <>

let dcl_dconss :=
  | dcons0 = dcl_dcons0; dconss = dcl_dcons1*; { dcons0 :: dconss }
  | ~ = dcl_dcons1*; <>

let dcl_ddata :=
  | DCL_INDUCTIVE; id = identifier; sids = dcl_sargs; ptm = dcl_ptm; EQUAL;
      dconss = dcl_dconss;
    { let pargs, b = ptm in
      let ptm = 
        List.fold_right (fun (id, a) acc ->
          PBind (a, Binder (id, acc))) pargs (PBase b)
      in
      let ss = List.map (fun sid -> SId sid) sids in
      let d =
        App (Inst (id, ss) ::
               List.map (fun (id, _) -> Id id) pargs)
      in
      let dconss =
        List.map (fun (id, targs) ->
          let tl = 
            List.fold_right (fun (rel, id, a) acc ->
              TBind (rel, a, Binder (id, acc))) targs (TBase d)
          in
          let ptl =
            List.fold_right (fun (id, a) acc ->
              PBind (a, Binder (id, acc))) pargs (PBase tl)
          in
          DCons (id, Binder (sids, ptl))) dconss
      in
      DData (id, Binder (sids, ptm), dconss) }

let dcl :=
  | ~ = dcl_dtm; <>
  | ~ = dcl_ddata; <>

let main :=
  | ~ = dcl*; EOF; <>
