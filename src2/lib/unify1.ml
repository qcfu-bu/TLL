open Fmt
open Bindlib
open Names
open Syntax1
open Equality1

type eqn = tm VMap.t * tm * tm
type eqns = eqn list
type map = (tm option * tm option) MMap.t

let rec fv ctx = function
  (* inference *)
  | Ann (m, a) -> VSet.union (fv ctx m) (fv ctx a)
  | Meta (_, ms) ->
      Array.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  (* core *)
  | Type _ -> VSet.empty
  | Var x -> (
      match VSet.find_opt x ctx with
      | Some _ -> VSet.empty
      | None -> VSet.singleton x)
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
  | Fix (_, bnd) ->
      let r, m = unbind bnd in
      fv (VSet.add r ctx) m
  (* data *)
  | Sigma (_, _, a, bnd) ->
      let x, b = unbind bnd in
      let fv1 = fv ctx a in
      let fv2 = fv (VSet.add x ctx) b in
      VSet.union fv1 fv2
  | Pair (_, _, m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Data (_, ms) ->
      Array.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Cons (_, ms) ->
      Array.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Match (m, bnd, cls) ->
      let x, mot = unbind bnd in
      let fv1 = fv ctx m in
      let fv2 = fv (VSet.add x ctx) mot in
      let fv3 =
        Array.fold_left
          (fun acc cl ->
            match cl with
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
  | Eq (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Refl -> VSet.empty
  | Rew (bnd, pf, m) ->
      let xs, a = unmbind bnd in
      let fv1 = fv (Array.fold_right VSet.add xs ctx) a in
      let fv2 = fv ctx pf in
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
  | End _ -> VSet.empty
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
  | Recv (_, m) -> fv ctx m
  | Send (_, m) -> fv ctx m
  | Close m -> fv ctx m

let rec occurs x = function
  (* inference *)
  | Ann (m, a) -> occurs x m || occurs x a
  | Meta (y, _) -> M.equal x y
  (* core *)
  | Pi (_, _, a, bnd) ->
      let _, b = unbind bnd in
      occurs x a || occurs x b
  | Lam (_, _, bnd) ->
      let _, m = unbind bnd in
      occurs x m
  | App (m, n) -> occurs x m || occurs x n
  | Let (_, m, bnd) ->
      let _, n = unbind bnd in
      occurs x m || occurs x n
  | Fix (_, bnd) ->
      let _, m = unbind bnd in
      occurs x m
  (* data *)
  | Sigma (_, _, a, bnd) ->
      let _, b = unbind bnd in
      occurs x a || occurs x b
  | Pair (_, _, m, n) -> occurs x m || occurs x n
  | Data (_, ms) -> Array.exists (occurs x) ms
  | Cons (_, ms) -> Array.exists (occurs x) ms
  | Match (m, bnd, cls) ->
      let _, a = unbind bnd in
      occurs x m || occurs x a
      || Array.exists
           (function
             | PPair (_, _, bnd) ->
                 let _, m = unmbind bnd in
                 occurs x m
             | PCons (_, bnd) ->
                 let _, m = unmbind bnd in
                 occurs x m)
           cls
  (* equality *)
  | Eq (m, n) -> occurs x m || occurs x n
  | Rew (bnd, pf, m) ->
      let _, a = unmbind bnd in
      occurs x a || occurs x pf || occurs x m
  (* monadic *)
  | IO a -> occurs x a
  | Return m -> occurs x m
  | MLet (m, bnd) ->
      let _, n = unbind bnd in
      occurs x m || occurs x n
  (* session *)
  | Act (_, _, a, bnd) ->
      let _, b = unbind bnd in
      occurs x a || occurs x b
  | Ch (_, a) -> occurs x a
  | Fork (a, bnd) ->
      let _, m = unbind bnd in
      occurs x a || occurs x m
  | Recv (_, m) -> occurs x m
  | Send (_, m) -> occurs x m
  | Close m -> occurs x m
  (* other *)
  | _ -> false
