open Fmt
open Names
open MParser
open Syntax0

let reserved =
  SSet.of_list
    [ "U"
    ; "L"
    ; "def"
    ; "theorem"
    ; "axiom"
    ; "param"
    ; "inductive"
    ; "where"
    ; "forall"
    ; "fun"
    ; "fix"
    ; "let"
    ; "in"
    ; "match"
    ; "as"
    ; "return"
    ; "with"
    ]

type ctx =
  { cs : int SMap.t
  ; ds : int SMap.t
  }

type 'a parser = ('a, ctx) MParser.t

let add_c c sz ctx = { ctx with cs = SMap.add c sz ctx.cs }
let add_d d sz ctx = { ctx with ds = SMap.add d sz ctx.ds }
let find_c c ctx = SMap.find_opt c ctx.cs
let find_d d ctx = SMap.find_opt d ctx.ds
let ( let* ) = bind
let choice ls = choice (List.map attempt ls)
let option p = option (attempt p)
let trivial : unit parser = any_char_or_nl >>$ ()

let rec nested_comment () : unit parser =
  let* _ = string "/-" in
  let* _ =
    many
      (let* opt =
         look_ahead (string "-/")
         >> return true
         <|> (nested_comment () <|> trivial >> return false)
       in
       if opt then
         zero
       else
         return ())
  in
  let* _ = string "-/" in
  return ()

let line_comment () : unit parser =
  let terminal = newline >>$ () <|> eof in
  let* _ = string "--" in
  let* _ =
    many
      (let* opt =
         look_ahead terminal >> return true <|> (trivial >> return false)
       in
       if opt then
         zero
       else
         return ())
  in
  let* _ = terminal in
  return ()

let ws : unit parser =
  many
    (choice
       [ blank >>$ (); newline >>$ (); nested_comment (); line_comment () ])
  >>$ ()

let kw s : unit parser = string s >> ws
let parens p = kw "(" >> p << kw ")"
let braces p = kw "{" >> p << kw "}"

let id_parser : id parser =
  let* s1 = many1_chars (letter <|> char '_') in
  let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
  let s = s1 ^ s2 in
  match SSet.find_opt s reserved with
  | Some _ -> fail (str "not a valid identifier(%s)" s)
  | None -> return s << ws

let pvar_parser () =
  let* id = id_parser in
  return (PVar id)

let pcons_parser () =
  let* ctx = get_user_state in
  let* id = id_parser in
  match find_c id ctx with
  | Some 0 -> return (PCons (id, []))
  | Some _ ->
    let* ids = many1 id_parser in
    return (PCons (id, ids))
  | _ -> zero

let pdata_parser () =
  let* ctx = get_user_state in
  let* id = id_parser in
  match find_d id ctx with
  | Some 0 -> return (PData (id, []))
  | Some _ ->
    let* ids = many1 id_parser in
    return (PData (id, ids))
  | _ -> zero

let rec p_parser () =
  let* _ = return () in
  choice [ pcons_parser (); pvar_parser (); parens (p_parser ()) ]

let rec type_parser () = kw "U" >>$ Type U <|> (kw "L" >>$ Type L)

and ann_parser () =
  let* a = kw "@[" >> tm_parser () << kw "]" in
  let* m = tm_parser () in
  return (Ann (a, m))

and argR_parser () =
  parens
    (let* ids = many1 id_parser in
     let* _ = kw ":" in
     let* a = tm_parser () in
     let arg = List.map (fun id -> (R, id, a)) ids in
     return arg)

and argN_parser () =
  braces
    (let* ids = many1 id_parser in
     let* _ = kw ":" in
     let* a = tm_parser () in
     let arg = List.map (fun id -> (N, id, a)) ids in
     return arg)

and args_parser () =
  let* args = many (argR_parser () <|> argN_parser ()) in
  let args = List.concat args in
  return args

and args1_parser () =
  let* args = many1 (argR_parser () <|> argN_parser ()) in
  let args = List.concat args in
  return args

and pi_parser () =
  let* _ = kw "∀" <|> kw "forall" in
  let* args = args1_parser () in
  let* srt = kw "→" <|> kw "->" >>$ U <|> (kw "⊸" <|> kw "-o" >>$ L) in
  let* b = tm_parser () in
  let t = List.fold_right (fun (r, id, a) b -> Pi (r, srt, id, a, b)) args b in
  return t

and lam_parser () =
  let* _ = kw "λ" <|> kw "fun" in
  let* args =
    many1
      (choice
         [ braces (id_parser >>= fun id -> return (N, id))
         ; (id_parser >>= fun id -> return (R, id))
         ])
  in
  let* srt = kw "→" <|> kw "->" >>$ U <|> (kw "⊸" <|> kw "-o" >>$ L) in
  let* m = tm_parser () in
  let lam = List.fold_right (fun (r, id) m -> Lam (r, srt, id, m)) args m in
  return lam

and fix_parser () =
  let* _ = kw "μ" <|> kw "fix" in
  let* id = id_parser in
  let* args =
    many1
      (choice
         [ braces (id_parser >>= fun id -> return (N, id))
         ; (id_parser >>= fun id -> return (R, id))
         ])
  in
  let* _ = kw "→" <|> kw "->" in
  let* m = tm_parser () in
  let lam = List.fold_right (fun (r, id) m -> Lam (r, U, id, m)) args m in
  return (Fix (id, lam))

and let_parser () =
  let* _ = kw "let" in
  let* r, id =
    choice
      [ braces (id_parser >>= fun id -> return (N, id))
      ; (id_parser >>= fun id -> return (R, id))
      ]
  in
  let* opt = option (kw ":" >> tm_parser ()) in
  let* _ = kw ":=" in
  let* m = tm_parser () in
  let m =
    match opt with
    | Some a -> Ann (a, m)
    | None -> m
  in
  let* _ = kw "in" in
  let* n = tm_parser () in
  return (Let (r, id, m, n))

and branch_parser () =
  let* _ = kw "|" in
  let* p = p_parser () in
  let* _ = kw "→" <|> kw "->" in
  let* rhs = tm_parser () in
  return (p, rhs)

and branches_parser () = many (branch_parser ())

and match_parser () =
  let* _ = kw "match" in
  let* m = tm_parser () in
  let* mot = mot_parser () in
  let* _ = kw "with" in
  let* cls = branches_parser () in
  return (Match (m, mot, cls))

and mot1_parser () =
  let* _ = kw "as" in
  let* id = id_parser in
  let* _ = kw "return" in
  let* a = tm_parser () in
  return (Mot1 (id, a))

and mot2_parser () =
  let* _ = kw "in" in
  let* p = pdata_parser () in
  let* _ = kw "return" in
  let* a = tm_parser () in
  return (Mot2 (p, a))

and mot3_parser () =
  let* _ = kw "as" in
  let* id = id_parser in
  let* _ = kw "in" in
  let* p = pdata_parser () in
  let* _ = kw "return" in
  let* a = tm_parser () in
  return (Mot3 (id, p, a))

and mot_parser () =
  choice [ mot3_parser (); mot1_parser (); mot2_parser (); return Mot0 ]

and arrowN_parser () =
  let* a = braces (tm_parser ()) in
  let* _ = kw "→" <|> kw "->" in
  let* b = tm_parser () in
  return (Pi (N, U, "", a, b))

and lolliN_parser () =
  let* a = braces (tm_parser ()) in
  let* _ = kw "⊸" <|> kw "-o" in
  let* b = tm_parser () in
  return (Pi (N, L, "", a, b))

and tm0_parser () =
  let* _ = return () in
  choice
    [ (id_parser >>= fun id -> return (Id id))
    ; type_parser ()
    ; ann_parser ()
    ; pi_parser ()
    ; arrowN_parser ()
    ; lolliN_parser ()
    ; lam_parser ()
    ; fix_parser ()
    ; let_parser ()
    ; match_parser ()
    ; parens (tm_parser ())
    ]

and tm1_parser () =
  let* hd = tm0_parser () in
  let* tl = many (tm0_parser ()) in
  match tl with
  | [] -> return hd
  | _ -> return (App (hd :: tl))

and tm2_parser () =
  let arrow_parser =
    let* _ = kw "→" <|> kw "->" in
    return (fun a b -> Pi (R, U, "", a, b))
  in
  let lolli_parser =
    let* _ = kw "⊸" <|> kw "-o" in
    return (fun a b -> Pi (R, L, "", a, b))
  in
  chain_right1 (tm1_parser ()) (arrow_parser <|> lolli_parser)

and tm_parser () = tm2_parser ()

let dtm_parser =
  let* r = kw "def" >>$ R <|> (kw "theorem" >>$ N) in
  let* id = id_parser in
  let* a_opt = option (kw ":" >> tm_parser ()) in
  let* _ = kw ":=" in
  let* m = tm_parser () in
  return (DTm (r, id, a_opt, m))

let rec make_tl a =
  match a with
  | Pi (r, U, id, a, b) ->
    let tl, sz = make_tl b in
    (TBind (r, id, a, tl), 1 + sz)
  | Pi (_, L, _, _, _) -> failwith "make_tl"
  | _ -> (TBase a, 0)

let cons_parser args =
  let* _ = kw "|" in
  let* c = id_parser in
  let* _ = kw ":" in
  let* a = tm_parser () in
  let tl, sz = make_tl a in
  let* _ = update_user_state (add_c c sz) in
  let ptl =
    List.fold_right (fun (_, x, a) ptl -> PBind (x, a, ptl)) args (PBase tl)
  in
  return (DCons (c, ptl))

let conss_parser args = many (cons_parser args)

let ddate_parser =
  let* _ = kw "inductive" in
  let* d = id_parser in
  let* args = args_parser () in
  let* _ = kw ":" in
  let* b = tm_parser () in
  let tl, sz = make_tl b in
  let* _ = update_user_state (add_d d sz) in
  let* _ = kw "where" in
  let* conss = conss_parser args in
  let ptl =
    List.fold_right (fun (_, x, a) ptl -> PBind (x, a, ptl)) args (PBase tl)
  in
  return (DData (d, ptl, conss))

let datom_parser =
  let* r = kw "axiom" >>$ N <|> (kw "param" >>$ R) in
  let* id = id_parser in
  let* _ = kw ":" in
  let* a = tm_parser () in
  return (DAtom (r, id, a))

let dcl_parser = choice [ dtm_parser; ddate_parser; datom_parser ]
let dcls_parser = many1 dcl_parser

let parse_string s =
  let ctx = { cs = SMap.empty; ds = SMap.empty } in
  parse_string (ws >> dcls_parser << eof) s ctx

let parse_channel ch =
  let ctx = { cs = SMap.empty; ds = SMap.empty } in
  parse_channel (ws >> dcls_parser << eof) ch ctx
