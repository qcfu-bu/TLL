open Bindlib
open Names
open Syntax
open Util
open Equality
open Context

type eqn =
  | EqSort of sort * sort
  | EqTm of Env.t * tm * tm
  | CheckTm of Ctx.t * Env.t * tm * tm

type eqns = eqn list
type mctx = tm IMeta.Map.t
type map0 = (sort, sort) mbinder SMeta.Map.t
type map1 = (sort, (tm, tm) mbinder) mbinder IMeta.Map.t

(* free sort variables *)
let rec fsv = function
  | SVar x -> SVar.Set.singleton x
  | SMeta (_, ss) -> fsvs ss
  | _ -> SVar.Set.empty

and fsvs ss =
  Array.fold_left (fun acc s -> SVar.Set.union acc (fsv s)) SVar.Set.empty ss

(* free term variables *)
let rec fv ctx = function
  (* inference *)
  | Ann (m, a) ->
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv ctx a in
    (SVar.Set.union fsv1 fsv2, Var.Set.union fv1 fv2)
  | IMeta (_, ss, ms) ->
    let fsv1 = fsvs ss in
    let fsv2, fv = fvs ctx ms in
    (SVar.Set.union fsv1 fsv2, fv)
  | PMeta _ -> (SVar.Set.empty, Var.Set.empty)
  (* core *)
  | Type s -> (fsv s, Var.Set.empty)
  | Var x -> (
    match Var.Set.find_opt x ctx with
    | Some _ -> (SVar.Set.empty, Var.Set.empty)
    | None -> (SVar.Set.empty, Var.Set.singleton x))
  | Const (_, ss) -> (fsvs ss, Var.Set.empty)
  | Pi (_, s, a, bnd) ->
    let x, b = unbind bnd in
    let fsv0 = fsv s in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (Var.Set.add x ctx) b in
    (SVar.Set.(union (union fsv0 fsv1) fsv2), Var.Set.union fv1 fv2)
  | Lam (_, s, a, bnd) ->
    let x, m = unbind bnd in
    let fsv0 = fsv s in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (Var.Set.add x ctx) m in
    (SVar.Set.(union (union fsv0 fsv1) fsv2), Var.Set.union fv1 fv2)
  | Fix (_, a, bnd) ->
    let x, m = unbind bnd in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (Var.Set.add x ctx) m in
    (SVar.Set.union fsv1 fsv2, Var.Set.union fv1 fv2)
  | App (m, n) ->
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv ctx n in
    (SVar.Set.union fsv1 fsv2, Var.Set.union fv1 fv2)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv (Var.Set.add x ctx) n in
    (SVar.Set.union fsv1 fsv2, Var.Set.union fv1 fv2)
  (* inductive *)
  | Ind (_, ss) -> (fsvs ss, Var.Set.empty)
  | Constr (_, ss) -> (fsvs ss, Var.Set.empty)
  | Match (ms, a, cls) ->
    let fsv1, fv1 =
      Array.fold_left
        (fun (acc0, acc1) (m, _) ->
          let fsv, fv = fv ctx m in
          (SVar.Set.union acc0 fsv, Var.Set.union acc1 fv))
        (SVar.Set.empty, Var.Set.empty)
        ms
    in
    let fsv2, fv2 = fv ctx a in
    let fsv3, fv3 =
      Array.fold_left
        (fun (acc0, acc1) (_, bnd) ->
          let xs, rhs = unmbind bnd in
          let ctx = Array.fold_left (fun ctx x -> Var.Set.add x ctx) ctx xs in
          let fsv, fv = fv ctx rhs in
          (SVar.Set.union acc0 fsv, Var.Set.union acc1 fv))
        (SVar.Set.empty, Var.Set.empty)
        cls
    in
    ( SVar.Set.(union (union fsv1 fsv2) fsv3)
    , Var.Set.(union (union fv1 fv2) fv3) )
  | Absurd -> (SVar.Set.empty, Var.Set.empty)
  (* record *)
  | Record (s, mp) ->
    let fsv1 = fsv s in
    let fsv2, fv =
      Proj.Map.fold
        (fun _ a (acc0, acc1) ->
          let fsv, fv = fv ctx a in
          (SVar.Set.union acc0 fsv, Var.Set.union acc1 fv))
        mp
        (SVar.Set.empty, Var.Set.empty)
    in
    (SVar.Set.union fsv1 fsv2, fv)
  | Struct (s, mp) ->
    let fsv1 = fsv s in
    let fsv2, fv =
      Proj.Map.fold
        (fun _ m (acc0, acc1) ->
          let fsv, fv = fv ctx m in
          (SVar.Set.union acc0 fsv, Var.Set.union acc1 fv))
        mp
        (SVar.Set.empty, Var.Set.empty)
    in
    (SVar.Set.union fsv1 fsv2, fv)
  | Proj (_, m) -> fv ctx m

and fvs ctx ms =
  Array.fold_left
    (fun (acc0, acc1) m ->
      let fsv, fv = fv ctx m in
      (SVar.Set.union acc0 fsv, Var.Set.union acc1 fv))
    (SVar.Set.empty, Var.Set.empty)
    ms

(* collect smeta variables *)
let rec meta_of_sort = function
  | SMeta (x, ss) ->
    let smeta = meta_of_sorts ss in
    SMeta.Set.add x smeta
  | _ -> SMeta.Set.empty

and meta_of_sorts ss =
  Array.fold_left
    (fun acc s -> SMeta.Set.union acc (meta_of_sort s))
    SMeta.Set.empty ss

(* collect imeta variables *)
let rec meta_of_tm = function
  (* inference *)
  | Ann (m, a) ->
    let smeta1, imeta1 = meta_of_tm m in
    let smeta2, imeta2 = meta_of_tm a in
    (SMeta.Set.union smeta1 smeta2, IMeta.Set.union imeta1 imeta2)
  | IMeta (x, ss, ms) ->
    let smeta1 = meta_of_sorts ss in
    let smeta2, imeta = meta_of_tms ms in
    (SMeta.Set.union smeta1 smeta2, IMeta.Set.add x imeta)
  | PMeta _ -> (SMeta.Set.empty, IMeta.Set.empty)
  (* core *)
  | Type s -> (meta_of_sort s, IMeta.Set.empty)
  | Var _ -> (SMeta.Set.empty, IMeta.Set.empty)
  | Const (_, ss) -> (meta_of_sorts ss, IMeta.Set.empty)
  | Pi (_, s, a, bnd) ->
    let x, b = unbind bnd in
    let smeta0 = meta_of_sort s in
    let smeta1, imeta1 = meta_of_tm a in
    let smeta2, imeta2 = meta_of_tm b in
    ( SMeta.Set.(union (union smeta0 smeta1) smeta2)
    , IMeta.Set.union imeta1 imeta2 )
  | Lam (_, s, a, bnd) ->
    let x, m = unbind bnd in
    let smeta0 = meta_of_sort s in
    let smeta1, imeta1 = meta_of_tm a in
    let smeta2, imeta2 = meta_of_tm m in
    ( SMeta.Set.(union (union smeta0 smeta1) smeta2)
    , IMeta.Set.union imeta1 imeta2 )
  | Fix (_, a, bnd) ->
    let x, m = unbind bnd in
    let smeta1, imeta1 = meta_of_tm a in
    let smeta2, imeta2 = meta_of_tm m in
    (SMeta.Set.union smeta1 smeta2, IMeta.Set.union imeta1 imeta2)
  | App (m, n) ->
    let smeta1, imeta1 = meta_of_tm m in
    let smeta2, imeta2 = meta_of_tm n in
    (SMeta.Set.union smeta1 smeta2, IMeta.Set.union imeta1 imeta2)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let smeta1, imeta1 = meta_of_tm m in
    let smeta2, imeta2 = meta_of_tm n in
    (SMeta.Set.union smeta1 smeta2, IMeta.Set.union imeta1 imeta2)
  (* inductive *)
  | Ind (_, ss) -> (meta_of_sorts ss, IMeta.Set.empty)
  | Constr (_, ss) -> (meta_of_sorts ss, IMeta.Set.empty)
  | Match (ms, a, cls) ->
    let smeta1, imeta1 =
      Array.fold_left
        (fun (acc0, acc1) (m, _) ->
          let smeta, imeta = meta_of_tm m in
          (SMeta.Set.union acc0 smeta, IMeta.Set.union acc1 imeta))
        (SMeta.Set.empty, IMeta.Set.empty)
        ms
    in
    let smeta2, imeta2 = meta_of_tm a in
    let smeta3, imeta3 =
      Array.fold_left
        (fun (acc0, acc1) (_, bnd) ->
          let xs, rhs = unmbind bnd in
          let smeta, imeta = meta_of_tm rhs in
          (SMeta.Set.union acc0 smeta, IMeta.Set.union acc1 imeta))
        (SMeta.Set.empty, IMeta.Set.empty)
        cls
    in
    ( SMeta.Set.(union (union smeta1 smeta2) smeta3)
    , IMeta.Set.(union (union imeta1 imeta2) imeta3) )
  | Absurd -> (SMeta.Set.empty, IMeta.Set.empty)
  (* record *)
  | Record (s, mp) ->
    let smeta1 = meta_of_sort s in
    let smeta2, imeta =
      Proj.Map.fold
        (fun _ a (acc0, acc1) ->
          let smeta, imeta = meta_of_tm a in
          (SMeta.Set.union acc0 smeta, IMeta.Set.union acc1 imeta))
        mp
        (SMeta.Set.empty, IMeta.Set.empty)
    in
    (SMeta.Set.union smeta1 smeta2, imeta)
  | Struct (s, mp) ->
    let smeta1 = meta_of_sort s in
    let smeta2, imeta =
      Proj.Map.fold
        (fun _ m (acc0, acc1) ->
          let smeta, imeta = meta_of_tm m in
          (SMeta.Set.union acc0 smeta, IMeta.Set.union acc1 imeta))
        mp
        (SMeta.Set.empty, IMeta.Set.empty)
    in
    (SMeta.Set.union smeta1 smeta2, imeta)
  | Proj (_, m) -> meta_of_tm m

and meta_of_tms ms =
  Array.fold_left
    (fun (acc0, acc1) m ->
      let smeta, imeta = meta_of_tm m in
      (SMeta.Set.union acc0 smeta, IMeta.Set.union acc1 imeta))
    (SMeta.Set.empty, IMeta.Set.empty)
    ms
