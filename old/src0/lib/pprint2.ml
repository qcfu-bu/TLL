open Fmt
open Names
open Syntax2

let rec pp_p fmt p =
  match p with
  | PVar x -> V.pp fmt x
  | PCons (c, []) -> C.pp fmt c
  | PCons (c, xs) -> pf fmt "(%a %a)" C.pp c pp_xs xs

and pp_xs fmt = function
  | [] -> ()
  | [ x ] -> pf fmt "%a" V.pp x
  | x :: xs -> pf fmt "%a %a" V.pp x pp_xs xs

let rec rel_gather r rxs =
  match rxs with
  | [] -> ([], [])
  | (r', x) :: rxs' ->
    if r' = r then
      let xs, rxs = rel_gather r rxs' in
      (x :: xs, rxs)
    else
      ([], rxs)

let rec lam_gather s m =
  match m with
  | Lam (t, abs) ->
    if s = t then
      let x, m = unbind_tm abs in
      let xs, m = lam_gather s m in
      (x :: xs, m)
    else
      ([], m)
  | m -> ([], m)

let rec pp_tm fmt = function
  | Var x -> V.pp fmt x
  | Lam (s, abs) -> (
    let x, m = unbind_tm abs in
    let xs, m = lam_gather s m in
    let xs = x :: xs in
    match s with
    | U -> pf fmt "@[fun %a ->@;<1 2>%a@]" pp_xs xs pp_tm m
    | L -> pf fmt "@[fun %a ->@;<1 2>%a@]" pp_xs xs pp_tm m)
  | App _ as m ->
    let m, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm m (list ~sep:sp pp_tm) ms
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    pf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  | Cons (c, ms) -> (
    match ms with
    | [] -> C.pp fmt c
    | _ -> pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms)
  | Match (s, m, cls) ->
    pf fmt "(@[<v 0>@[match %a<%a>with@]@;<1 0>@[%a@]@]" pp_tm m pp_sort s
      pp_cls cls
  | Fix m ->
    let x, m = unbind_tm m in
    let xs, m = lam_gather U m in
    let xs = x :: xs in
    pf fmt "@[fix %a ->@;<1 2>%a@]" pp_xs xs pp_tm m
  | Box -> pf fmt "□"

and pp_tms fmt ms = pf fmt "[%a]" (list ~sep:semi pp_tm) ms

and pp_cl fmt abs =
  let p, m = unbindp_tm abs in
  pf fmt "| %a ->@;<1 2>%a" pp_p p pp_tm m

and pp_cls fmt cls =
  match cls with
  | [] -> ()
  | [ cl ] -> pf fmt "@[%a@]" pp_cl cl
  | cl :: cls -> pf fmt "@[%a@]@;<1 0>%a" pp_cl cl pp_cls cls

let pp_dcons fmt (DCons (c, sz)) = pf fmt "| %a := %d" C.pp c sz

let rec pp_dconss fmt = function
  | [] -> ()
  | [ dcons ] -> pf fmt "@[%a@]" pp_dcons dcons
  | dcons :: dconss -> pf fmt "@[%a@]@;<1 0>%a" pp_dcons dcons pp_dconss dconss

let pp_dcl fmt = function
  | DTm (x, m) -> pf fmt "@[def %a :=@;<1 2>%a@]" V.pp x pp_tm m
  | DData (d, dconss) ->
    pf fmt "@[<v 0>@[inductive %a where@]@;<1 0>%a@]" D.pp d pp_dconss dconss
  | DAtom x -> pf fmt "@[param %a@]" V.pp x

let rec pp_dcls fmt dcls =
  match dcls with
  | [] -> ()
  | [ dcl ] -> pf fmt "%a@." pp_dcl dcl
  | dcl :: dcls -> pf fmt "%a@.@.%a" pp_dcl dcl pp_dcls dcls
