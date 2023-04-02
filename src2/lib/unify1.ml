open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Pprint1

type eqn =
  | Eqn0 of sort * sort (* sort equations *)
  | Eqn1 of env * tm * tm (* term equations *)

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
  | Const _ -> VSet.empty
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

(* meta variable occurences *)
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
  (* data *)
  | Sigma (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs x a || occurs x b
  | Pair (_, _, m, n) -> occurs x m || occurs x n
  | Data (_, _, ms) -> List.exists (occurs x) ms
  | Cons (_, _, ms, ns) -> List.exists (occurs x) (ms @ ns)
  | Match (m, bnd, cls) ->
    let _, a = unbind bnd in
    occurs x m || occurs x a
    || List.exists
         (function
           | PPair (_, _, bnd) ->
             let _, m = unmbind bnd in
             occurs x m
           | PCons (_, bnd) ->
             let _, m = unmbind bnd in
             occurs x m)
         cls
  (* equality *)
  | Eq (a, m, n) -> occurs x a || occurs x m || occurs x n
  | Refl m -> occurs x m
  | Rew (bnd, p, m) ->
    let _, mot = unmbind bnd in
    occurs x mot || occurs x p || occurs x m
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
  | Recv m -> occurs x m
  | Send m -> occurs x m
  | Close m -> occurs x m
  (* other *)
  | _ -> false

(* Alpha simplification *)
let rec asimpl = function
  | Eqn0 (s1, s2) -> (
    if eq_sort s1 s2 then
      []
    else
      match (s1, s2) with
      | SMeta _, _ -> [ Eqn0 (s1, s2) ]
      | _, SMeta _ -> [ Eqn0 (s2, s1) ]
      | _ -> failwith "asimpl_Eqn0")
  | Eqn1 (env, m1, m2) -> (
    if eq_tm [| Beta; Iota |] env m1 m2 then
      []
    else
      match (m1, m2) with
      (* inference *)
      | Meta _, _ -> [ Eqn1 (env, m1, m2) ]
      | _, Meta _ -> [ Eqn1 (env, m2, m1) ]
      (* core *)
      | Type s1, Type s2 -> [ Eqn0 (s1, s2) ]
      | Var x1, Var x2 when eq_vars x1 x2 -> []
      | Const (x1, ss1), Const (x2, ss2) when eq_vars x1 x2 ->
        List.map2 (fun s1 s2 -> Eqn0 (s1, s2)) ss1 ss2
      | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) when rel1 = rel2 ->
        let _, b1, b2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, a1, a2)) in
        let eqns2 = asimpl (Eqn1 (env, b1, b2)) in
        Eqn0 (s1, s2) :: (eqns1 @ eqns2)
      | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) when rel1 = rel2 ->
        let _, m1, m2 = unbind2 bnd1 bnd2 in
        Eqn0 (s1, s2) :: asimpl (Eqn1 (env, m1, m2))
      | App _, App _ ->
        let hd1, sp1 = unApps m1 in
        let hd2, sp2 = unApps m2 in
        let eqns1 = asimpl (Eqn1 (env, hd1, hd2)) in
        let eqns2 =
          List.fold_right2
            (fun m n acc -> asimpl (Eqn1 (env, m, n)) @ acc)
            sp1 sp2 []
        in
        eqns1 @ eqns2
      | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) when rel1 = rel2 ->
        let _, n1, n2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, m1, m2)) in
        let eqns2 = asimpl (Eqn1 (env, n1, n2)) in
        eqns1 @ eqns2
      (* data *)
      | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) when rel1 = rel2
        ->
        let _, b1, b2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, a1, a2)) in
        let eqns2 = asimpl (Eqn1 (env, b1, b2)) in
        Eqn0 (s1, s2) :: (eqns1 @ eqns2)
      | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) when rel1 = rel2 ->
        let eqns1 = asimpl (Eqn1 (env, m1, m2)) in
        let eqns2 = asimpl (Eqn1 (env, n1, n2)) in
        Eqn0 (s1, s2) :: (eqns1 @ eqns2)
      | Data (d1, ss1, ms1), Data (d2, ss2, ms2) when D.equal d1 d2 ->
        let eqns1 = List.map2 (fun s1 s2 -> Eqn0 (s1, s2)) ss1 ss2 in
        let eqns2 =
          List.fold_right2
            (fun m1 m2 acc -> asimpl (Eqn1 (env, m1, m2)) @ acc)
            ms1 ms2 []
        in
        eqns1 @ eqns2
      | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) when C.equal c1 c2 ->
        let eqns1 = List.map2 (fun s1 s2 -> Eqn0 (s1, s2)) ss1 ss2 in
        let eqns2 =
          List.fold_right2
            (fun m1 m2 acc -> asimpl (Eqn1 (env, m1, m2)) @ acc)
            (ms1 @ ns1) (ms2 @ ns2) []
        in
        eqns1 @ eqns2
      | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
        let _, mot1, mot2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, m1, m2)) in
        let eqns2 = asimpl (Eqn1 (env, mot1, mot2)) in
        let eqns3 =
          List.fold_right2
            (fun cl1 cl2 acc ->
              match (cl1, cl2) with
              | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) when rel1 = rel2
                ->
                let _, m1, m2 = unmbind2 bnd1 bnd2 in
                Eqn0 (s1, s2) :: (asimpl (Eqn1 (env, m1, m2)) @ acc)
              | PCons (c1, bnd1), PCons (c2, bnd2) when C.equal c1 c2 ->
                let _, m1, m2 = unmbind2 bnd1 bnd2 in
                asimpl (Eqn1 (env, m1, m2)) @ acc
              | _ -> failwith "asimpl_Match")
            cls1 cls2 []
        in
        eqns1 @ eqns2 @ eqns3
      (* equality *)
      | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
        let eqns1 = asimpl (Eqn1 (env, a1, a2)) in
        let eqns2 = asimpl (Eqn1 (env, m1, m2)) in
        let eqns3 = asimpl (Eqn1 (env, n1, n2)) in
        eqns1 @ eqns2 @ eqns3
      | Refl m1, Refl m2 -> asimpl (Eqn1 (env, m1, m2))
      | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
        let _, mot1, mot2 = unmbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, mot1, mot2)) in
        let eqns2 = asimpl (Eqn1 (env, p1, p2)) in
        let eqns3 = asimpl (Eqn1 (env, m1, m2)) in
        eqns1 @ eqns2 @ eqns3
      (* monadic *)
      | IO a1, IO a2 -> asimpl (Eqn1 (env, a1, a2))
      | Return m1, Return m2 -> asimpl (Eqn1 (env, m1, m2))
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        let _, n1, n2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, m1, m2)) in
        let eqns2 = asimpl (Eqn1 (env, n1, n2)) in
        eqns1 @ eqns2
      (* session *)
      | Proto, Proto -> []
      | End, End -> []
      | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2)
        when rel1 = rel2 && rol1 = rol2 ->
        let _, b1, b2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, a1, a2)) in
        let eqns2 = asimpl (Eqn1 (env, b1, b2)) in
        eqns1 @ eqns2
      | Ch (rol1, a1), Ch (rol2, a2) when rol1 = rol2 ->
        asimpl (Eqn1 (env, a1, a2))
      | Open prim1, Open prim2 when prim1 = prim2 -> []
      | Fork (a1, bnd1), Fork (a2, bnd2) ->
        let _, m1, m2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (Eqn1 (env, a1, a2)) in
        let eqns2 = asimpl (Eqn1 (env, m1, m2)) in
        eqns1 @ eqns2
      | Recv m1, Recv m2 -> asimpl (Eqn1 (env, m1, m2))
      | Send m1, Send m2 -> asimpl (Eqn1 (env, m1, m2))
      | Close m1, Close m2 -> asimpl (Eqn1 (env, m1, m2))
      | _ -> failwith "asimpl")

(* Beta/Delta/Iota simplification *)
let rec simpl eqn =
  try asimpl eqn with
  | _ -> (
    match eqn with
    | Eqn0 (s1, s2) -> (
      if eq_sort s1 s2 then
        []
      else
        match (s1, s2) with
        | SMeta _, _ -> [ Eqn0 (s1, s2) ]
        | _, SMeta _ -> [ Eqn0 (s2, s1) ]
        | _ -> failwith "simpl_Eqn0")
    | Eqn1 (env, m1, m2) -> (
      let m1 = whnf [| Beta; Iota |] env m1 in
      let m2 = whnf [| Beta; Iota |] env m2 in
      match (m1, m2) with
      (* inference *)
      | Meta _, _ -> [ Eqn1 (env, m1, m2) ]
      | _, Meta _ -> [ Eqn1 (env, m2, m1) ]
      (* core *)
      | Type s1, Type s2 -> [ Eqn0 (s1, s2) ]
      | Var x1, Var x2 when eq_vars x1 x2 -> []
      | Const (x1, ss1), Const (x2, ss2) when eq_vars x1 x2 ->
        List.map2 (fun s1 s2 -> Eqn0 (s1, s2)) ss1 ss2
      | Const (x, ss), _ -> (
        match VMap.find_opt x env with
        | Some entry -> simpl (Eqn1 (env, entry.scheme ss, m2))
        | None -> [])
      | _, Const (y, ss) -> (
        match VMap.find_opt y env with
        | Some entry -> simpl (Eqn1 (env, m1, entry.scheme ss))
        | None -> [])
      | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) when rel1 = rel2 ->
        let _, b1, b2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, a1, a2)) in
        let eqns2 = simpl (Eqn1 (env, b1, b2)) in
        Eqn0 (s1, s2) :: (eqns1 @ eqns2)
      | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) when rel1 = rel2 ->
        let _, m1, m2 = unbind2 bnd1 bnd2 in
        Eqn0 (s1, s2) :: simpl (Eqn1 (env, m1, m2))
      | App _, App _ -> (
        try
          let hd1, sp1 = unApps m1 in
          let hd2, sp2 = unApps m2 in
          let eqns1 = simpl (Eqn1 (env, hd1, hd2)) in
          let eqns2 =
            List.fold_right2
              (fun m n acc -> simpl (Eqn1 (env, m, n)) @ acc)
              sp1 sp2 []
          in
          eqns1 @ eqns2
        with
        | _ ->
          let m1 = whnf rd_all env m1 in
          let m2 = whnf rd_all env m2 in
          simpl (Eqn1 (env, m1, m2)))
      | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) when rel1 = rel2 ->
        let _, n1, n2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, m1, m2)) in
        let eqns2 = simpl (Eqn1 (env, n1, n2)) in
        eqns1 @ eqns2
      (* data *)
      | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) when rel1 = rel2
        ->
        let _, b1, b2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, a1, a2)) in
        let eqns2 = simpl (Eqn1 (env, b1, b2)) in
        Eqn0 (s1, s2) :: (eqns1 @ eqns2)
      | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) when rel1 = rel2 ->
        let eqns1 = simpl (Eqn1 (env, m1, m2)) in
        let eqns2 = simpl (Eqn1 (env, n1, n2)) in
        Eqn0 (s1, s2) :: (eqns1 @ eqns2)
      | Data (d1, ss1, ms1), Data (d2, ss2, ms2) when D.equal d1 d2 ->
        let eqns1 = List.map2 (fun s1 s2 -> Eqn0 (s1, s2)) ss1 ss2 in
        let eqns2 =
          List.fold_right2
            (fun m1 m2 acc -> simpl (Eqn1 (env, m1, m2)) @ acc)
            ms1 ms2 []
        in
        eqns1 @ eqns2
      | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) when C.equal c1 c2 ->
        let eqns1 = List.map2 (fun s1 s2 -> Eqn0 (s1, s2)) ss1 ss2 in
        let eqns2 =
          List.fold_right2
            (fun m1 m2 acc -> simpl (Eqn1 (env, m1, m2)) @ acc)
            (ms1 @ ns1) (ms2 @ ns2) []
        in
        eqns1 @ eqns2
      | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
        let _, mot1, mot2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, m1, m2)) in
        let eqns2 = simpl (Eqn1 (env, mot1, mot2)) in
        let eqns3 =
          List.fold_right2
            (fun cl1 cl2 acc ->
              match (cl1, cl2) with
              | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) when rel1 = rel2
                ->
                let _, m1, m2 = unmbind2 bnd1 bnd2 in
                Eqn0 (s1, s2) :: (simpl (Eqn1 (env, m1, m2)) @ acc)
              | PCons (c1, bnd1), PCons (c2, bnd2) when C.equal c1 c2 ->
                let _, m1, m2 = unmbind2 bnd1 bnd2 in
                simpl (Eqn1 (env, m1, m2)) @ acc
              | _ -> failwith "simpl_Match")
            cls1 cls2 []
        in
        eqns1 @ eqns2 @ eqns3
      (* equality *)
      | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
        let eqns1 = simpl (Eqn1 (env, a1, a2)) in
        let eqns2 = simpl (Eqn1 (env, m1, m2)) in
        let eqns3 = simpl (Eqn1 (env, n1, n2)) in
        eqns1 @ eqns2 @ eqns3
      | Refl m1, Refl m2 -> simpl (Eqn1 (env, m1, m2))
      | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
        let _, mot1, mot2 = unmbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, mot1, mot2)) in
        let eqns2 = simpl (Eqn1 (env, p1, p2)) in
        let eqns3 = simpl (Eqn1 (env, m1, m2)) in
        eqns1 @ eqns2 @ eqns3
      (* monadic *)
      | IO a1, IO a2 -> simpl (Eqn1 (env, a1, a2))
      | Return m1, Return m2 -> simpl (Eqn1 (env, m1, m2))
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        let _, n1, n2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, m1, m2)) in
        let eqns2 = simpl (Eqn1 (env, n1, n2)) in
        eqns1 @ eqns2
      (* session *)
      | Proto, Proto -> []
      | End, End -> []
      | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2)
        when rel1 = rel2 && rol1 = rol2 ->
        let _, b1, b2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, a1, a2)) in
        let eqns2 = simpl (Eqn1 (env, b1, b2)) in
        eqns1 @ eqns2
      | Ch (rol1, a1), Ch (rol2, a2) when rol1 = rol2 ->
        simpl (Eqn1 (env, a1, a2))
      | Open prim1, Open prim2 when prim1 = prim2 -> []
      | Fork (a1, bnd1), Fork (a2, bnd2) ->
        let _, m1, m2 = unbind2 bnd1 bnd2 in
        let eqns1 = simpl (Eqn1 (env, a1, a2)) in
        let eqns2 = simpl (Eqn1 (env, m1, m2)) in
        eqns1 @ eqns2
      | Recv m1, Recv m2 -> simpl (Eqn1 (env, m1, m2))
      | Send m1, Send m2 -> simpl (Eqn1 (env, m1, m2))
      | Close m1, Close m2 -> simpl (Eqn1 (env, m1, m2))
      (* other *)
      | _ -> []))

let solve ((map0, map1) : map0 * map1) eqn =
  let meta_spine sp =
    List.map
      (function
        | Var x -> x
        | _ -> V.mk "_")
      sp
  in
  match eqn with
  | Eqn0 (s1, s2) -> (
    match (s1, s2) with
    | SMeta _, SMeta _ -> (map0, map1)
    | SMeta x, _ -> (MMap.add x s2 map0, map1)
    | _ -> (map0, map1))
  | Eqn1 (env, m1, m2) -> (
    let m1 = whnf [| Beta; Iota |] env m1 in
    let m2 = whnf [| Beta; Iota |] env m2 in
    match (m1, m2) with
    | Meta _, Meta _ -> (map0, map1)
    | Meta (x, xs), _ ->
      if occurs x m2 then
        (map0, map1)
      else
        let xs = meta_spine xs in
        if VSet.subset (fv VSet.empty m2) (VSet.of_list xs) then
          let bnd = bind_mvar (Array.of_list xs) (lift_tm m2) in
          (map0, MMap.add x (Some (unbox bnd), None) map1)
        else
          (map0, map1)
    | _ -> (map0, map1))

let resolve_sort (map0 : map0) = function
  | SMeta x as s -> (
    match MMap.find_opt x map0 with
    | Some s -> s
    | None -> s)
  | s -> s

let resolve_tm ((map0, map1) : map0 * map1) m =
  let rec resolve = function
    (* inference *)
    | Ann (m, a) -> Ann (resolve m, resolve a)
    | Meta (x, ms) as m -> (
      match MMap.find_opt x map1 with
      | Some (Some bnd, _) ->
        let m = msubst bnd (Array.of_list ms) in
        resolve m
      | _ -> m)
    (* core *)
    | Type s -> Type (resolve_sort map0 s)
    | Const (x, ss) ->
      let ss = List.map (resolve_sort map0) ss in
      Const (x, ss)
    | Pi (rel, s, a, bnd) ->
      let x, b = unbind bnd in
      let s = resolve_sort map0 s in
      let a = resolve a in
      let b = lift_tm (resolve b) in
      Pi (rel, s, a, unbox (bind_var x b))
    | Lam (rel, s, bnd) ->
      let x, m = unbind bnd in
      let s = resolve_sort map0 s in
      let m = lift_tm (resolve m) in
      Lam (rel, s, unbox (bind_var x m))
    | App (m, n) -> App (resolve m, resolve n)
    | Let (rel, m, bnd) ->
      let x, n = unbind bnd in
      let m = resolve m in
      let n = lift_tm (resolve n) in
      Let (rel, m, unbox (bind_var x n))
    (* data *)
    | Sigma (rel, s, a, bnd) ->
      let x, b = unbind bnd in
      let s = resolve_sort map0 s in
      let a = resolve a in
      let b = lift_tm (resolve b) in
      Sigma (rel, s, a, unbox (bind_var x b))
    | Pair (rel, s, m, n) ->
      let s = resolve_sort map0 s in
      let m = resolve m in
      let n = resolve n in
      Pair (rel, s, m, n)
    | Data (d, ss, ms) ->
      let ss = List.map (resolve_sort map0) ss in
      let ms = List.map resolve ms in
      Data (d, ss, ms)
    | Cons (c, ss, ms, ns) ->
      let ss = List.map (resolve_sort map0) ss in
      let ms = List.map resolve ms in
      let ns = List.map resolve ns in
      Cons (c, ss, ms, ns)
    | Match (m, bnd, cls) ->
      let x, mot = unbind bnd in
      let m = resolve m in
      let mot = lift_tm (resolve mot) in
      let cls =
        List.map
          (function
            | PPair (rel, s, bnd) ->
              let xs, n = unmbind bnd in
              let s = resolve_sort map0 s in
              let n = lift_tm (resolve n) in
              PPair (rel, s, unbox (bind_mvar xs n))
            | PCons (c, bnd) ->
              let xs, n = unmbind bnd in
              let n = lift_tm (resolve n) in
              PCons (c, unbox (bind_mvar xs n)))
          cls
      in
      Match (m, unbox (bind_var x mot), cls)
    (* equality *)
    | Eq (a, m, n) -> Eq (resolve a, resolve m, resolve n)
    | Refl m -> Refl (resolve m)
    | Rew (bnd, p, m) ->
      let xs, mot = unmbind bnd in
      let mot = lift_tm (resolve mot) in
      let p = resolve p in
      let m = resolve m in
      Rew (unbox (bind_mvar xs mot), p, m)
    (* monadic *)
    | IO a -> IO (resolve a)
    | Return m -> Return (resolve m)
    | MLet (m, bnd) ->
      let x, n = unbind bnd in
      let m = resolve m in
      let n = lift_tm (resolve n) in
      MLet (m, unbox (bind_var x n))
    (* session *)
    | Act (rel, rol, a, bnd) ->
      let x, b = unbind bnd in
      let a = resolve a in
      let b = lift_tm (resolve b) in
      Act (rel, rol, a, unbox (bind_var x b))
    | Ch (rol, a) -> Ch (rol, resolve a)
    | Fork (a, bnd) ->
      let x, m = unbind bnd in
      let a = resolve a in
      let m = lift_tm (resolve m) in
      Fork (a, unbox (bind_var x m))
    | Recv m -> Recv (resolve m)
    | Send m -> Send (resolve m)
    | Close m -> Close (resolve m)
    (* other *)
    | m -> m
  in
  resolve m

let rec resolve_param lift resolve map = function
  | PBase a -> PBase (resolve map a)
  | PBind (a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_param lift (resolve_param lift resolve map b) in
    PBind (a, unbox (bind_var x b))

let rec resolve_tele map = function
  | TBase a -> TBase (resolve_tm map a)
  | TBind (rel, a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_tele (resolve_tele map b) in
    TBind (rel, a, unbox (bind_var x b))

let resolve_dcons map (DCons (c, sch)) =
  let xs, ptl = unmbind sch in
  let ptl = resolve_param lift_tele resolve_tele map ptl in
  DCons (c, unbox (bind_mvar xs (lift_param lift_tele ptl)))

let resolve_dcl map = function
  | DTm (rel, x, sch) ->
    let xs, (a, m) = unmbind sch in
    let a = lift_tm (resolve_tm map a) in
    let m = lift_tm (resolve_tm map m) in
    DTm (rel, x, unbox (bind_mvar xs (box_pair a m)))
  | DData (d, sch, dconss) ->
    let xs, ptm = unmbind sch in
    let ptm = resolve_param lift_tm resolve_tm map ptm in
    let sch = bind_mvar xs (lift_param lift_tm ptm) in
    let dconss = List.map (resolve_dcons map) dconss in
    DData (d, unbox sch, dconss)

let resolve_dcls map dcls = List.map (resolve_dcl map) dcls

let rec unify ((map0, map1) as map : map0 * map1) eqns =
  let eqns =
    List.map
      (function
        | Eqn0 (s1, s2) -> Eqn0 (resolve_sort map0 s1, resolve_sort map0 s2)
        | Eqn1 (env, m1, m2) -> Eqn1 (env, resolve_tm map m1, resolve_tm map m2))
      eqns
  in
  match List.concat_map simpl eqns with
  | [] -> map
  | eqn :: eqns ->
    let map = solve map eqn in
    unify map eqns
