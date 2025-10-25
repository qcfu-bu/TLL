open Fmt
open Bindlib
open Names
open Syntax1

let rec pp_p fmt = function
  | PVar x -> Var.pp fmt x
  | PAbsurd -> pf fmt "!!"
  | PConstr (c, []) -> pf fmt "%a" Constr.pp c
  | PConstr (c, ps) -> pf fmt "(%a %a)" Constr.pp c (pp_ps " ") ps

and pp_ps sep fmt = function
  | [] -> ()
  | [ p ] -> pp_p fmt p
  | p :: ps -> pf fmt "%a%s%a" pp_p p sep (pp_ps sep) ps

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"
  | SVar x -> SVar.pp fmt x
  | SMeta (x, _) -> pf fmt "??%a" SMeta.pp x

let rec pp_sorts fmt = function
  | [] -> ()
  | [ s ] -> pp_sort fmt s
  | s :: ss -> pf fmt "%a,%a" pp_sort s pp_sorts ss

let pp_relv fmt = function
  | N -> pf fmt "N"
  | R -> pf fmt "R"

let pp_role fmt = function
  | true -> pf fmt "⇑"
  | false -> pf fmt "⇓"

let pp_modifier fmt = function
  | R -> pf fmt "program"
  | N -> pf fmt "logical"

let rec pp_rxs fmt = function
  | [] -> ()
  | [ (r, x, a) ] -> (
    match r with
    | N -> pf fmt "{%a : %a}" Var.pp x pp_tm a
    | R -> pf fmt "(%a : %a)" Var.pp x pp_tm a)
  | (r, x, a) :: rxs -> (
    match r with
    | R -> pf fmt "(%a : %a)@;<1 0>%a" Var.pp x pp_tm a pp_rxs rxs
    | N -> pf fmt "{%a : %a}@;<1 0>%a" Var.pp x pp_tm a pp_rxs rxs)

and pp_tm fmt = function
  (* inference *)
  | Ann (m, a) -> pf fmt "@[(%a@;<1 2>: %a)@]" pp_tm m pp_tm a
  | IMeta (x, ss, xs) ->
    pf fmt "?%a[%d;%d]" IMeta.pp x (List.length ss) (List.length xs)
  | PMeta x -> pf fmt "#%a" Var.pp x
  (* core *)
  | Type U -> pf fmt "U"
  | Type L -> pf fmt "L"
  | Type s -> pf fmt "Type‹%a›" pp_sort s
  | Var x -> Var.pp fmt x
  | Const (x, []) -> pf fmt "%a" Const.pp x
  | Const (x, ss) -> pf fmt "%a‹%a›" Const.pp x pp_sorts ss
  | Pi (R, U, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" Var.pp x pp_tm a pp_tm b
    else
      pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (N, U, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ {%a :@;<1 2>%a} ->@]@;<1 2>%a@]" Var.pp x pp_tm a pp_tm b
    else
      pf fmt "@[{%a} ->@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (R, L, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ (%a :@;<1 2>%a) -o@]@;<1 2>%a@]" Var.pp x pp_tm a pp_tm b
    else
      pf fmt "@[%a -o@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (N, L, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ {%a :@;<1 2>%a} -o@]@;<1 2>%a@]" Var.pp x pp_tm a pp_tm b
    else
      pf fmt "@[{%a} -o@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (R, s, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[forall‹%a›(%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_sort s Var.pp x
      pp_tm a pp_tm b
  | Pi (N, s, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[forall‹%a›{%a :@;<1 2>%a},@]@;<1 2>%a@]" pp_sort s Var.pp x
      pp_tm a pp_tm b
  | Fun (_, a, bnd) ->
    let x, cls = unbind bnd in
    pf fmt "@[<v 0>@[(fun %a :@;<1 2>@[%a@]@]@;<1 0>@[<v 0>%a)@]@]" Var.pp x
      pp_tm a (pp_cls ", ") cls
  | App _ as m ->
    let hd, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm hd (list ~sep:sp pp_tm) ms
  | Let (R, m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a :=@;<1 2>%a@]@;<1 0>in@;<1 0>%a@]" Var.pp x pp_tm m pp_tm
      n
  | Let (N, m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let {%a} :=@;<1 2>%a@]@;<1 0>in@;<1 0>%a@]" Var.pp x pp_tm m
      pp_tm n
  (* inductive *)
  | Ind (d, [], [], []) -> pf fmt "%a" Ind.pp d
  | Ind (d, [], ms, ns) ->
    pf fmt "@[(%a@;<1 2>@[%a@])@]" Ind.pp d (list ~sep:sp pp_tm) (ms @ ns)
  | Ind (d, ss, [], []) -> pf fmt "%a‹%a›" Ind.pp d pp_sorts ss
  | Ind (d, ss, ms, ns) ->
    pf fmt "@[(%a‹%a›@;<1 2>@[%a@])@]" Ind.pp d pp_sorts ss (list ~sep:sp pp_tm)
      (ms @ ns)
  | Constr (c, [], [], []) -> pf fmt "%a" Constr.pp c
  | Constr (c, ss, [], []) -> pf fmt "%a‹%a›" Constr.pp c pp_sorts ss
  | Constr (c, ss, ns, ms) ->
    pf fmt "@[(%a‹%a›@;<1 2>@[%a@])@]" Constr.pp c pp_sorts ss
      (list ~sep:sp pp_tm) (ns @ ms)
  | Match (_, ms, a, cls) ->
    pf fmt "@[<v 0>(@[match %a in@;<1 2>%a@;<1 0>with@]@;<1 0>@[<v 0>%a@])@]"
      (list ~sep:comma pp_tm) ms pp_tm a (pp_cls ", ") cls
  (* monad *)
  | IO a -> pf fmt "IO %a" pp_tm a
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a <-@;<1 2>%a@]@;<1 0>in@;<1 0>%a@]" Var.pp x pp_tm m pp_tm
      n
  (* primitive types *)
  | Int_t -> pf fmt "int"
  | Char_t -> pf fmt "char"
  | String_t -> pf fmt "string"
  (* primitive terms *)
  | Int i -> pf fmt "%d" i
  | Char c -> pf fmt "%c" c
  | String s -> pf fmt "\"%s\"" (String.escaped s)
  (* primitive operators *)
  | Neg m -> pf fmt "@[(__neg__@;<1 2>@[%a@])@]" pp_tm m
  | Add (m, n) ->
    pf fmt "@[(__add__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Sub (m, n) ->
    pf fmt "@[(__sub__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Mul (m, n) ->
    pf fmt "@[(__mul__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Div (m, n) ->
    pf fmt "@[(__div__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Mod (m, n) ->
    pf fmt "@[(__mod__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Lte (m, n) ->
    pf fmt "@[(__lte__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Gte (m, n) ->
    pf fmt "@[(__gte__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Lt (m, n) -> pf fmt "@[(__lt__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Gt (m, n) -> pf fmt "@[(__gt__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Eq (m, n) -> pf fmt "@[(__eq__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Chr m -> pf fmt "@[(__chr__@;<1 2>@[%a@])@]" pp_tm m
  | Ord m -> pf fmt "@[(__ord__@;<1 2>@[%a@])@]" pp_tm m
  | Push (m, n) ->
    pf fmt "@[(__push__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Cat (m, n) ->
    pf fmt "@[(__cat__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Size m -> pf fmt "@[(__size__@;<1 2>@[%a@])@]" pp_tm m
  | Indx (m, n) -> pf fmt "@[%a.[%a]@]" pp_tm m pp_tm n
  (* primitive sessions *)
  | Proto -> pf fmt "proto"
  | End -> pf fmt "•"
  | Act (R, role, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[%a(%a :@;<1 2>%a) ⇒@]@;<1 2>%a@]" pp_role role Var.pp x pp_tm a
      pp_tm b
  | Act (N, role, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[%a{%a :@;<1 2>%a} ⇒@]@;<1 2>%a@]" pp_role role Var.pp x pp_tm a
      pp_tm b
  | Ch (true, m) -> pf fmt "ch⟨%a⟩" pp_tm m
  | Ch (false, m) -> pf fmt "hc⟨%a⟩" pp_tm m
  (* primitive effects *)
  | Print m -> pf fmt "@[print@;<1 2>%a@]" pp_tm m
  | Prerr m -> pf fmt "@[prerr@;<1 2>%a@]" pp_tm m
  | ReadLn m -> pf fmt "@[readln@;<1 2>%a@]" pp_tm m
  | Fork m -> pf fmt "@[fork@;<1 2>%a@]" pp_tm m
  | Send m -> pf fmt "@[send@;<1 2>%a@]" pp_tm m
  | Recv m -> pf fmt "@[recv@;<1 2>%a@]" pp_tm m
  | Close m -> pf fmt "@[close@;<1 2>%a@]" pp_tm m
  (* magic *)
  | Magic a -> pf fmt "#magic[%a]" pp_tm a

and pp_cl sep fmt cl =
  let ps, m_opt = unbind_ps cl in
  match m_opt with
  | Some m -> pf fmt "| @[%a =>@;<1 0>%a@]" (pp_ps sep) ps pp_tm m
  | None -> pf fmt "| @[%a =>@]" (pp_ps sep) ps

and pp_cls sep fmt = function
  | [] -> ()
  | [ cl ] -> (pp_cl sep) fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" (pp_cl sep) cl (pp_cls sep) cls

let rec unpack_param = function
  | PBase tele -> ([], tele)
  | PBind (a, bnd) ->
    let x, param = unbind bnd in
    let args, tele = unpack_param param in
    ((x, a) :: args, tele)

let rec pp_sargs fmt = function
  | [] -> ()
  | [ x ] -> SVar.pp fmt x
  | x :: xs -> pf fmt "%a,%a" SVar.pp x pp_sargs xs

let rec pp_args fmt = function
  | [] -> ()
  | [ (x, a) ] -> pf fmt "(%a : %a)" Var.pp x pp_tm a
  | (x, a) :: args -> pf fmt "(%a : %a) %a" Var.pp x pp_tm a pp_args args

let rec pp_arity fmt = function
  | TBase a -> pp_tm fmt a
  | TBind (_, a, bnd) ->
    let x, tele = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a" Var.pp x pp_tm a pp_arity tele
    else
      pf fmt "%a ->@;<1 2>%a" pp_tm a pp_arity tele

let rec pp_tele fmt = function
  | TBase a -> pf fmt ": %a" pp_tm a
  | TBind (R, a, bnd) ->
    let x, tele = unbind bnd in
    pf fmt "(%a : %a)@;<1 0>%a" Var.pp x pp_tm a pp_tele tele
  | TBind (N, a, bnd) ->
    let x, tele = unbind bnd in
    pf fmt "{%a : %a}@;<1 0>%a" Var.pp x pp_tm a pp_tele tele

let pp_dconstr xs args fmt dconstr =
  let rec pack_param args param =
    match (args, param) with
    | [], PBase tele -> tele
    | (x, _) :: args, PBind (_, bnd) -> pack_param args (subst bnd (Var x))
    | _ -> failwith "pp_dconstr.pack_param"
  in
  match dconstr with
  | c, sch ->
    let param = msubst sch (Array.map (fun x -> SVar x) xs) in
    let tele = pack_param args param in
    pf fmt "| @[%a@;<1 2>@[%a@]@]" Constr.pp c pp_tele tele

let rec pp_dconstrs xs args fmt = function
  | [] -> ()
  | [ dconstr ] -> pp_dconstr xs args fmt dconstr
  | dconstr :: dconstrs ->
    pf fmt "%a@;<1 0>%a" (pp_dconstr xs args) dconstr (pp_dconstrs xs args)
      dconstrs

let pp_dcl fmt = function
  | Definition { name = x; relv; scheme = sch } ->
    let xs, (m, a) = unmbind sch in
    pf fmt
      "@[@[<v 0>#[%a]@;<1 0>def@] %a‹%a› :@;<1 2>@[%a@]@;<1 0>:=@;<1 2>@[%a@]@]"
      pp_modifier relv Const.pp x pp_sargs (Array.to_list xs) pp_tm a pp_tm m
  | Inductive { name = d; relv; arity; dconstrs } ->
    let xs, param = unmbind arity in
    let args, tele = unpack_param param in
    pf fmt
      "@[<v 0>@[@[<v 0>#[%a]@;\
       <1 0>inductive@] %a‹%a› %a:@;\
       <1 2>@[%a@]@;\
       <1 0>where@]@;\
       <1 0>%a@]"
      pp_modifier relv Ind.pp d pp_sargs (Array.to_list xs) pp_args args
      pp_arity tele (pp_dconstrs xs args) dconstrs
  | Extern { name = x; relv; scheme = sch } -> (
    let xs, (m_opt, a) = unmbind sch in
    match m_opt with
    | Some m ->
      pf fmt
        "@[@[<v 0>#[%a]@;\
         <1 0>extern@] %a‹%a› :@;\
         <1 2>@[%a@]@;\
         <1 0>:=@;\
         <1 2>@[%a@]@]"
        pp_modifier relv Const.pp x pp_sargs (Array.to_list xs) pp_tm a pp_tm m
    | None ->
      pf fmt "@[@[<v 0>#[%a]@;<1 0>extern@] %a‹%a› :@;<1 2>@[%a@]@]" pp_modifier
        relv Const.pp x pp_sargs (Array.to_list xs) pp_tm a)

let pp_dcls fmt dcls =
  let break fmt _ = pf fmt "@.@." in
  pf fmt "%a" (list ~sep:break pp_dcl) dcls
