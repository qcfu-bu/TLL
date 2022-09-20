open Fmt
open Names
open Syntax1

let rec pp_p fmt p =
  match p with
  | PVar x -> V.pp fmt x
  | PData (d, []) -> D.pp fmt d
  | PData (d, xs) -> pf fmt "(%a%a)" D.pp d pp_xs xs
  | PCons (c, []) -> C.pp fmt c
  | PCons (c, xs) -> pf fmt "(%a%a)" C.pp c pp_xs xs

and pp_xs fmt = function
  | [] -> ()
  | [ x ] -> pf fmt " %a" V.pp x
  | x :: xs -> pf fmt " %a%a" V.pp x pp_xs xs

let rec gather = function
  | Lam abs ->
    let x, m = unbind_tm abs in
    let xs, m = gather m in
    (x :: xs, m)
  | m -> ([], m)

let rec pp_tm fmt = function
  | Ann (a, m) -> pf fmt "@[(@@[%a]@,%a)@]" pp_tm a pp_tm m
  | Meta (x, _) -> pf fmt "%a" M.pp x
  | Type s -> pp_srt fmt s
  | Var x -> V.pp fmt x
  | Pi (r, s, a, abs) -> (
    let x, b = unbind_tm abs in
    match (r, s, occurs_tm x b) with
    | N, U, false -> pf fmt "@[{%a} ->@;<1 2>%a@]" pp_tm a pp_tm b
    | N, U, true ->
      pf fmt "@[@[∀ {%a :@;<1 2>%a} ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | N, L, false -> pf fmt "@[{%a} -o@;<1 2>%a@]" pp_tm a pp_tm b
    | N, L, true ->
      pf fmt "@[@[∀ {%a :@;<1 2>%a} -o@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | R, U, false -> pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tm b
    | R, U, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | R, L, false -> pf fmt "@[%a -o@;<1 2>%a@]" pp_tm a pp_tm b
    | R, L, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) -o@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b)
  | Lam abs ->
    let x, m = unbind_tm abs in
    let xs, m = gather m in
    pf fmt "@[fun %a%a =>@;<1 2>%a@]" V.pp x pp_xs xs pp_tm m
  | App _ as m ->
    let m, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm m (list ~sep:sp pp_tm) ms
  | Let (r, m, abs) -> (
    let x, n = unbind_tm abs in
    match r with
    | N ->
      pf fmt "@[@[prf %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm
        n
    | R ->
      pf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm
        n)
  | Data (d, ms) -> (
    match ms with
    | [] -> D.pp fmt d
    | _ -> pf fmt "@[(%a@;<1 2>%a)@]" D.pp d (list ~sep:sp pp_tm) ms)
  | Cons (c, ms) -> (
    match ms with
    | [] -> C.pp fmt c
    | _ -> pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms)
  | Match (m, mot, cls) ->
    pf fmt "@[<v 0>@[match %a%a@;<1 0>with@]@;<1 0>@[%a@]end@]" pp_tm m pp_mot
      mot pp_cls cls
  | Fix m ->
    let x, m = unbind_tm m in
    let xs, m = gather m in
    pf fmt "@[fix %a%a =>@;<1 2>%a@]" V.pp x pp_xs xs pp_tm m

and pp_tms fmt ms = pf fmt "[%a]" (list ~sep:semi pp_tm) ms

and pp_mot fmt = function
  | Mot0 -> ()
  | Mot1 abs ->
    let x, a = unbind_tm abs in
    pf fmt " as %a return@;<1 2>%a" V.pp x pp_tm a
  | Mot2 abs ->
    let p, a = unbindp_tm abs in
    pf fmt " in %a return@;<1 2>%a" pp_p p pp_tm a
  | Mot3 abs ->
    let x, abs = unbind_ptm abs in
    let p, a = unbindp_tm abs in
    pf fmt " as %a in %a return@;<1 2>%a" V.pp x pp_p p pp_tm a

and pp_cl fmt abs =
  let p, m = unbindp_tm abs in
  pf fmt "| %a =>@;<1 2>%a" pp_p p pp_tm m

and pp_cls fmt cls =
  match cls with
  | [] -> ()
  | [ cl ] -> pf fmt "@[%a@]" pp_cl cl
  | cl :: cls -> pf fmt "@[%a@]@;<1 2>%a" pp_cl cl pp_cls cls

let rec pp_ptl fmt = function
  | PBase tl -> pf fmt ":@;<1 2>%a" pp_tl tl
  | PBind (r, a, abs) -> (
    let x, ptl = unbind_ptl abs in
    match r with
    | N -> pf fmt "{%a : %a} %a" V.pp x pp_tm a pp_ptl ptl
    | R -> pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_ptl ptl)

and pp_tl fmt = function
  | TBase b -> pp_tm fmt b
  | TBind (r, a, abs) -> (
    let x, tl = unbind_tl abs in
    match (r, occurs_tl x tl) with
    | N, false -> pf fmt "@[{%a} ->@;<1 2>%a@]" pp_tm a pp_tl tl
    | N, true ->
      pf fmt "@[@[∀ {%a :@;<1 2>%a} ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tl tl
    | R, false -> pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tl tl
    | R, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tl tl)

let pp_dcons fmt (DCons (c, ptl)) = pf fmt "| %a %a" C.pp c pp_ptl ptl

let rec pp_dconss fmt = function
  | [] -> ()
  | [ dcons ] -> pf fmt "@[%a@]" pp_dcons dcons
  | dcons :: dconss -> pf fmt "@[%a@]@;<1 2>%a" pp_dcons dcons pp_dconss dconss

let pp_dcl fmt = function
  | DTm (r, x, a_opt, m) -> (
    match (r, a_opt) with
    | N, Some a ->
      pf fmt "@[theorem %a :@;<1 2>%a :=@;<1 2>%a@]" V.pp x pp_tm a pp_tm m
    | N, None -> pf fmt "@[theorem %a :=@;<1 2>%a@]" V.pp x pp_tm m
    | R, Some a ->
      pf fmt "@[definition %a :@;<1 2>%a :=@;<1 2>%a@]" V.pp x pp_tm a pp_tm m
    | R, None -> pf fmt "@[definition %a :=@;<1 2>%a@]" V.pp x pp_tm m)
  | DData (d, ptl, dconss) ->
    pf fmt "@[<v 0>@[inductive %a %a where@]@;<1 2>%a@]" D.pp d pp_ptl ptl
      pp_dconss dconss
  | DAtom (r, x, a) -> (
    match r with
    | N -> pf fmt "@[axiom %a :@;<1 2>%a@]" V.pp x pp_tm a
    | R -> pf fmt "@[parameter %a :@;<1 2>%a@]" V.pp x pp_tm a)

let rec pp_dcls fmt dcls =
  match dcls with
  | [] -> ()
  | [ dcl ] -> pf fmt "%a@." pp_dcl dcl
  | dcl :: dcls -> pf fmt "%a@.@.%a" pp_dcl dcl pp_dcls dcls
