open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Pprint1

type eqn = tm VMap.t * tm * tm
type eqns = eqn list
type map0 = sort MMap.t
type map1 = ((tm, tm) mbinder option * tm option) MMap.t

let pp_map0 fmt (map0 : map0) =
  let aux fmt (map0 : map0) =
    MMap.iter (fun x s -> pf fmt "%a := %a@;<1 0>" M.pp x pp_sort s) map0
  in
  pf fmt "@[<v 0>{@;<1 2>@[<v 0>%a@]@;<1 0>}@]" aux map0

let pp_map1 fmt (map1 : map1) =
  let aux fmt map1 =
    MMap.iter
      (fun x (opt1, opt2) ->
        match (opt1, opt2) with
        | Some bnd, Some a ->
          let _, m = unmbind bnd in
          pf fmt "%a := @[%a : %a@]@;<1 0>" M.pp x pp_tm m pp_tm a
        | None, Some a -> pf fmt "%a := ?? : @[%a@]@;<1 0>" M.pp x pp_tm a
        | Some bnd, None ->
          let _, m = unmbind bnd in
          pf fmt "%a := @[%a@] : ??@;<1 0>" M.pp x pp_tm m
        | None, None -> pf fmt "%a := ?? : ??@;<1 0>" M.pp x)
      map1
  in
  pf fmt "@[<v 0>{@;<1 2>@[<v 0>%a@]@;<1 0>}@]" aux map1

let bad_magic env m1 m2 =
  pr "@[bad_magic(@;<1 2>%a@;<1 0>::::::@;<1 2>%a)@]@.@." pp_tm m1 pp_tm m2

(* free term variables *)
let rec fv ctx = function
  (* inference *)
  | Ann (m, a) -> VSet.union (fv ctx m) (fv ctx a)
  | Meta (_, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  (* core *)
  | Type _ -> VSet.empty
  | Var x -> (
    match VSet.find_opt x ctx with
    | Some _ -> VSet.empty
    | None -> VSet.singleton x)
  | Const (x, _) -> VSet.singleton x
  | Pi (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Lam (_, _, bnd) ->
    let x, m = unbind bnd in
    fv (VSet.add x ctx) m
  | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) n in
    VSet.union fv1 fv2
  (* data *)
  | Sigma (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Pair (_, _, m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Data (_, _, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Cons (_, _, ms, ns) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty (ms @ ns)
  | Match (m, bnd, cls) ->
    let x, mot = unbind bnd in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) mot in
    let fv3 =
      List.fold_left
        (fun acc -> function
          | PPair (_, _, bnd) ->
            let xs, m = unmbind bnd in
            fv (Array.fold_right VSet.add xs ctx) m
          | PCons (_, bnd) ->
            let xs, m = unmbind bnd in
            fv (Array.fold_right VSet.add xs ctx) m)
        VSet.empty cls
    in
    VSet.union (VSet.union fv1 fv2) fv3
  (* equality *)
  | Eq (a, m, n) -> VSet.union (VSet.union (fv ctx a) (fv ctx m)) (fv ctx n)
  | Refl m -> fv ctx m
  | Rew (bnd, p, m) ->
    let xs, mot = unmbind bnd in
    let fv1 = fv (Array.fold_right VSet.add xs ctx) mot in
    let fv2 = fv ctx p in
    let fv3 = fv ctx m in
    VSet.union (VSet.union fv1 fv2) fv3
  (* monadic *)
  | IO a -> fv ctx a
  | Return m -> fv ctx m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) n in
    VSet.union fv1 fv2
  (* session *)
  | Proto -> VSet.empty
  | End -> VSet.empty
  | Act (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Ch (_, a) -> fv ctx a
  | Open _ -> VSet.empty
  | Fork (a, bnd) ->
    let x, m = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  | Recv m -> fv ctx m
  | Send m -> fv ctx m
  | Close m -> fv ctx m
