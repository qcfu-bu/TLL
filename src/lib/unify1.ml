open Fmt
open Names
open Syntax1
open Equality1

type eqn = tm VMap.t * tm * tm
type eqns = eqn list

type map = (tm_opt * tm_opt) MMap.t

let rec fv ctx = function
  (* inference *)
  | Ann (m, a) -> VSet.union (fv ctx m) (fv ctx a)
  | Meta (_, ms) ->
    List.fold_left
      (fun acc m -> VSet.union acc (fv ctx m))
      VSet.empty ms
  (* core *)
  | Type _ -> VSet.empty
  | Var x ->
    (match VSet.find_opt x ctx with
     | Some _ -> VSet.empty
     | None -> VSet.singleton x)
  | Pi (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Lam (_, _, abs) ->
    let (x, a_opt), m = unbind_ann abs in
    let fv1 =
      Option.fold
        ~none:VSet.empty
        ~some:(fv ctx)
        a_opt
    in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Let (_, m, abs) ->
    let (x, a_opt), n = unbind_ann abs in
    let fv1 =
      Option.fold
        ~none:VSet.empty
        ~some:(fv ctx)
        a_opt
    in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  (* data *)
  | Sig (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Pair (_, _, m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Data (_, ms) ->
    List.fold_left
      (fun acc m -> VSet.union acc (fv ctx m))
      VSet.empty ms
  | Cons (_, ms) ->
    List.fold_left
      (fun acc m -> VSet.union acc (fv ctx m))
      VSet.empty ms
  | Match (m, mot, cls) ->
    let fv1 = fv ctx m in
    let fv2 =
      Option.fold
        ~none:VSet.empty
        ~some:(fun abs ->
            let x, a = unbind_tm abs in
            fv (VSet.add x ctx) a)
        mot
    in
    let fv3 = 
      List.fold_left
        (fun acc pabs ->
           let p, m = unbindp_tm pabs in
           let xs = xs_of_p p in
           let ctx = VSet.union (VSet.of_list xs) ctx in
           VSet.union acc (fv ctx m))
        VSet.empty cls
    in
    VSet.union (VSet.union fv1 fv2) fv3
  (* equality *)
  | Eq (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Refl -> VSet.empty
  | Rew (abs, pf, m) ->
    let (x, y), a = unbind_tm2 abs in
    let fv1 = fv (VSet.add x (VSet.add y ctx)) a in
    let fv2 = fv ctx pf in
    let fv3 = fv ctx m in
    VSet.union (VSet.union fv1 fv2) fv3
  (* moandic *)
  | IO a -> fv ctx a
  | Return m -> fv ctx m
  | Do (m, abs) ->
    let (x, a_opt), n = unbind_ann abs in
    let fv1 = fv ctx m in
    let fv2 =
      Option.fold
        ~none:VSet.empty
        ~some:(fv ctx)
        a_opt
    in
    let fv3 = fv (VSet.add x ctx) n in
    VSet.union (VSet.union fv1 fv2) fv3
  (* session *)
  | Proto -> VSet.empty
  | End _ -> VSet.empty
  | Act (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Ch (_, a) -> fv ctx a
  | Open _ -> VSet.empty
  | Fork (a, abs) ->
    let x, m = unbind_tm abs in
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
  | Pi (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Lam (_, _, abs) ->
    let (_, a_opt), m = unbind_ann abs in
    let b1 =
      Option.fold
        ~none:false
        ~some:(occurs x)
        a_opt
    in
    let b2 = occurs x m in
    b1 || b2
  | App (m, n) -> occurs x m || occurs x n
  | Let (_, m, abs) -> 
    let (_, a_opt), n = unbind_ann abs in
    let b1 = occurs x m in
    let b2 = 
      Option.fold
        ~none:false
        ~some:(occurs x)
        a_opt
    in
    let b3 = occurs x n in
    b1 || b2 || b3
  (* data *)
  | Sig (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Pair (_, _, m, n) ->
    occurs x m || occurs x n
  | Data (_, ms) -> List.exists (occurs x) ms
  | Cons (_, ms) -> List.exists (occurs x) ms
  | Match (m, mot, cls) ->
    let b1 = occurs x m in
    let b2 = 
      Option.fold
        ~none:false
        ~some:(fun abs ->
            let _, a = unbind_tm abs in
            occurs x a)
        mot
    in
    let b3 =
      List.exists
        (fun abs ->
           let _, m = unbindp_tm abs in
           occurs x m)
        cls
    in
    b1 || b2 || b3
  (* equality *)
  | Eq (m, n) -> occurs x m || occurs x n
  | Rew (abs, pf, m) ->
    let _, a = unbind_tm2 abs in
    occurs x a || occurs x pf || occurs x m
  (* monadic *)
  | IO a -> occurs x a
  | Return m -> occurs x m
  | Do (m, abs) ->
    let (_, a_opt), n = unbind_ann abs in
    let b1 = occurs x m in
    let b2 =
      Option.fold
        ~none:false
        ~some:(occurs x)
        a_opt
    in
    let b3 = occurs x n in
    b1 || b2 || b3
  (* session *)
  | Act (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Ch (_, a) -> occurs x a
  | Fork (a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Recv (_, m) -> occurs x m
  | Send (_, m) -> occurs x m
  | Close m -> occurs x m
  (* other *)
  | _ -> false

