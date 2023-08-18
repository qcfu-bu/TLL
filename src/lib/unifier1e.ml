open Fmt
open Bindlib
open Names
open Syntax1
open Context1e
open Equality1e
open Constraint1e
open Pprint1

(* subst meta-variables *)
type smeta_map = (sort, sort) mbinder SMeta.Map.t
type imeta_map = (sort, (tm, tm) mbinder) mbinder IMeta.Map.t
type meta_map = smeta_map * imeta_map

let pp_smeta fmt (smeta_map : smeta_map) =
  let aux fmt smeta_map =
    SMeta.Map.iter
      (fun x bnd ->
        let _, s = unmbind bnd in
        pf fmt "??%a <= %a@;<1 0>" SMeta.pp x pp_sort s)
      smeta_map
  in
  pf fmt "@[<v 0>smeta_meta {|@;<1 2>@[<v 0>%a@]@;<1 0>|}@]" aux smeta_map

let pp_imeta fmt (imeta_map : imeta_map) =
  let aux fmt imeta_map =
    IMeta.Map.iter
      (fun x bnd ->
        let _, bnd = unmbind bnd in
        let _, m = unmbind bnd in
        pf fmt "?%a <= %a@;<1 0>" IMeta.pp x pp_tm m)
      imeta_map
  in
  pf fmt "@[<v 0>imeta_meta {|@;<1 2>@[<v 0>%a@]@;<1 0>|}@]" aux imeta_map

let pp_meta fmt (meta_map : meta_map) =
  let smeta_map, imeta_map = meta_map in
  pf fmt "@[<v 0>%a@;<1 0>%a@]" pp_smeta smeta_map pp_imeta imeta_map

let rec resolve_sort (smeta_map : smeta_map) = function
  | SMeta (x, ss) as s -> (
    match SMeta.Map.find_opt x smeta_map with
    | Some bnd -> resolve_sort smeta_map (msubst bnd (Array.of_list ss))
    | None -> s)
  | s -> s

let resolve_tm (meta_map : meta_map) m =
  let smeta_map, imeta_map = meta_map in
  let aux_sort s = lift_sort (resolve_sort smeta_map s) in
  let rec aux_tm = function
    (* inference *)
    | Ann (m, a) -> _Ann (aux_tm m) (aux_tm a)
    | IMeta (x, ss, xs) as m -> (
      match IMeta.Map.find_opt x imeta_map with
      | Some bnd -> (
        let ss0, bnd0 = unmbind bnd in
        let xs0, m0 = unmbind bnd0 in
        try
          let bnd = msubst bnd (Array.of_list ss) in
          let m = msubst bnd (Array.of_list xs) in
          aux_tm m
        with
        | _ ->
          failwith "resolve_tm_failed(%a, [%a;%a] => %a)" pp_tm m
            (array ~sep:sp SVar.pp) ss0 (array ~sep:sp Var.pp) xs0 pp_tm m0)
      | None -> lift_tm m)
    | PMeta x -> _PMeta x
    (* core *)
    | Type s -> _Type (aux_sort s)
    | Var x -> _Var x
    | Const (x, ss) ->
      let ss = List.map aux_sort ss in
      _Const x (box_list ss)
    | Pi (relv, s, a, bnd) ->
      let x, b = unbind bnd in
      _Pi relv (aux_sort s) (aux_tm a) (bind_var x (aux_tm b))
    | Fun (guard, a, bnd) ->
      let x, cls = unbind bnd in
      let cls =
        List.map
          (fun cl ->
            let ps, rhs_opt = unbind_ps cl in
            let rhs_opt = Option.map (fun rhs -> aux_tm rhs) rhs_opt in
            bind_ps ps (box_opt rhs_opt))
          cls
      in
      _Fun guard (aux_tm a) (bind_var x (box_list cls))
    | App (m, n) -> _App (aux_tm m) (aux_tm n)
    | Let (relv, m, bnd) ->
      let x, n = unbind bnd in
      _Let relv (aux_tm m) (bind_var x (aux_tm n))
    (* inductive *)
    | Ind (d, ss, ms, ns) ->
      let ss = List.map aux_sort ss in
      let ms = List.map aux_tm ms in
      let ns = List.map aux_tm ns in
      _Ind d (box_list ss) (box_list ms) (box_list ns)
    | Constr (c, ss, ms, ns) ->
      let ss = List.map aux_sort ss in
      let ms = List.map aux_tm ms in
      let ns = List.map aux_tm ns in
      _Constr c (box_list ss) (box_list ms) (box_list ns)
    | Match (guard, ms, a, cls) ->
      let ms = List.map aux_tm ms in
      let cls =
        List.map
          (fun cl ->
            let ps, rhs_opt = unbind_ps cl in
            let rhs_opt = Option.map (fun rhs -> aux_tm rhs) rhs_opt in
            bind_ps ps (box_opt rhs_opt))
          cls
      in
      _Match guard (box_list ms) (aux_tm a) (box_list cls)
    (* monad *)
    | IO a -> _IO (aux_tm a)
    | Return m -> _Return (aux_tm m)
    | MLet (m, bnd) ->
      let x, n = unbind bnd in
      _MLet (aux_tm m) (bind_var x (aux_tm n))
    (* magic *)
    | Magic a -> _Magic (aux_tm a)
  in
  Debug.exec (fun () -> pr "@[resolve_attempt(%a)@]@." pp_tm m);
  let m_resolved = unbox (aux_tm m) in
  Debug.exec (fun () ->
      pr "@[resolve_tm(@;<1 2>@[%a@]@;<1 2>=>@;<1 2>@[%a@])@]@.@." pp_tm m pp_tm
        m_resolved);
  m_resolved

let resolve_scheme lift resolve (meta_map : meta_map) sch =
  let xs, body = unmbind sch in
  let body = lift (resolve meta_map body) in
  unbox (bind_mvar xs body)

let resolve_param lift resolve (meta_map : meta_map) param =
  let rec aux = function
    | PBase a -> PBase (resolve meta_map a)
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      let a = resolve_tm meta_map a in
      let b = lift_param lift (aux b) in
      PBind (a, unbox (bind_var x b))
  in
  aux param

let resolve_tele (meta_map : meta_map) tele =
  let rec aux = function
    | TBase a -> TBase (resolve_tm meta_map a)
    | TBind (relv, a, bnd) ->
      let x, b = unbind bnd in
      let a = resolve_tm meta_map a in
      let b = lift_tele (aux b) in
      TBind (relv, a, unbox (bind_var x b))
  in
  aux tele

let resolve_dconstr (meta_map : meta_map) (c, sch) =
  let sch =
    resolve_scheme (lift_param lift_tele)
      (resolve_param lift_tele resolve_tele)
      meta_map sch
  in
  (c, sch)

let resolve_dconstrs (meta_map : meta_map) dconstrs =
  List.map (resolve_dconstr meta_map) dconstrs

let resolve_dcl (meta_map : meta_map) = function
  | Definition { name; relv; scheme = sch } ->
    let sch =
      resolve_scheme
        (fun (m, a) -> box_pair (lift_tm m) (lift_tm a))
        (fun meta_map (m, a) -> (resolve_tm meta_map m, resolve_tm meta_map a))
        meta_map sch
    in
    Definition { name; relv; scheme = sch }
  | Inductive { name; relv; arity; dconstrs } ->
    let arity =
      resolve_scheme (lift_param lift_tele)
        (resolve_param lift_tele resolve_tele)
        meta_map arity
    in
    let dconstrs = resolve_dconstrs meta_map dconstrs in
    Inductive { name; relv; arity; dconstrs }
  | Extern { name; relv; scheme = sch } ->
    let sch = resolve_scheme lift_tm resolve_tm meta_map sch in
    Extern { name; relv; scheme = sch }

let resolve_dcls meta_map dcls = List.map (resolve_dcl meta_map) dcls

let map_pmeta f m =
  let rec aux m =
    match m with
    (* inference *)
    | Ann (m, a) -> _Ann (aux m) (aux a)
    | IMeta (x, ss, ms) ->
      let ss = List.map lift_sort ss in
      let ms = List.map aux ms in
      _IMeta x (box_list ss) (box_list ms)
    | PMeta x -> f aux x
    (* core *)
    | Type s -> _Type (lift_sort s)
    | Var x -> _Var x
    | Const (x, ss) ->
      let ss = List.map lift_sort ss in
      _Const x (box_list ss)
    | Pi (relv, s, a, bnd) ->
      let x, b = unbind bnd in
      _Pi relv (lift_sort s) (aux a) (bind_var x (aux b))
    | Fun (guard, a, bnd) ->
      let x, cls = unbind bnd in
      let cls =
        List.map
          (fun cl ->
            let ps, rhs_opt = unbind_ps cl in
            let rhs_opt = Option.map (fun rhs -> aux rhs) rhs_opt in
            bind_ps ps (box_opt rhs_opt))
          cls
      in
      let cls = box_list cls in
      _Fun guard (aux a) (bind_var x cls)
    | App (m, n) -> _App (aux m) (aux n)
    | Let (relv, m, bnd) ->
      let x, n = unbind bnd in
      _Let relv (aux m) (bind_var x (aux n))
    (* inductive *)
    | Ind (d, ss, ms, ns) ->
      let ss = List.map lift_sort ss in
      let ms = List.map aux ms in
      let ns = List.map aux ns in
      _Ind d (box_list ss) (box_list ms) (box_list ns)
    | Constr (c, ss, ms, ns) ->
      let ss = List.map lift_sort ss in
      let ms = List.map aux ms in
      let ns = List.map aux ns in
      _Constr c (box_list ss) (box_list ms) (box_list ns)
    | Match (guard, ms, a, cls) ->
      let ms = List.map aux ms in
      let cls =
        List.map
          (fun cl ->
            let ps, rhs_opt = unbind_ps cl in
            let rhs_opt = Option.map (fun rhs -> aux rhs) rhs_opt in
            bind_ps ps (box_opt rhs_opt))
          cls
      in
      _Match guard (box_list ms) (aux a) (box_list cls)
    (* monad *)
    | IO a -> _IO (aux a)
    | Return m -> _Return (aux m)
    | MLet (m, bnd) ->
      let x, n = unbind bnd in
      _MLet (aux m) (bind_var x (aux n))
    (* magic *)
    | Magic a -> _Magic (aux a)
  in
  unbox (aux m)

(* substitute pmeta variables *)
let subst_pmeta var_map m =
  map_pmeta
    (fun self x ->
      match Var.Map.find_opt x var_map with
      | Some m -> self m
      | None -> _PMeta x)
    m

(* demote pmeta variables *)
let demote_pmeta m = map_pmeta (fun _ x -> _Var x) m

(* substitute and demote pmeta variables *)
let resolve_pmeta var_map m =
  map_pmeta
    (fun self x ->
      match Var.Map.find_opt x var_map with
      | Some m -> self m
      | None -> _Var x)
    m

(* occurs checking *)
let rec occurs_sort x = function
  | SMeta (y, ss) -> SMeta.equal x y || List.exists (occurs_sort x) ss
  | _ -> false

let occurs_tm x m =
  let rec aux = function
    (* inference *)
    | Ann (m, a) -> aux m || aux a
    | IMeta (y, _, ms) -> IMeta.equal x y || List.exists aux ms
    | PMeta _ -> false
    (* core *)
    | Type _ -> false
    | Var _ -> false
    | Const _ -> false
    | Pi (_, _, a, bnd) ->
      let _, b = unbind bnd in
      aux a || aux b
    | Fun (_, a, bnd) ->
      let _, cls = unbind bnd in
      aux a
      || List.exists
           (fun (_, bnd) ->
             let _, rhs_opt = unmbind bnd in
             match rhs_opt with
             | Some rhs -> aux rhs
             | None -> false)
           cls
    | App (m, n) -> aux m || aux n
    | Let (_, m, bnd) ->
      let _, n = unbind bnd in
      aux m || aux n
    (* inductive *)
    | Ind (_, _, ms, ns) -> List.exists aux (ms @ ns)
    | Constr (_, _, ms, ns) -> List.exists aux (ms @ ns)
    | Match (_, ms, a, cls) ->
      List.exists aux ms || aux a
      || List.exists
           (fun (_, bnd) ->
             let _, rhs_opt = unmbind bnd in
             match rhs_opt with
             | Some rhs -> aux rhs
             | None -> false)
           cls
    (* monad *)
    | IO a -> aux a
    | Return m -> aux m
    | MLet (m, bnd) ->
      let _, n = unbind bnd in
      aux m || aux n
    (* magic *)
    | Magic a -> aux a
  in
  aux m

let rec simpl_iprbm ?(expand = false) eqn =
  let open IPrbm in
  let imeta_blocked m =
    let rec blocked_spine ms =
      List.exists
        (fun m ->
          match m with
          | IMeta _ -> true
          | _ -> blocked m)
        ms
    and blocked = function
      | App _ as m -> (
        match unApps m with
        | Fun _, ms -> blocked_spine ms
        | IMeta _, _ -> true
        | hd, _ -> blocked hd)
      | Match (_, ms, _, _) -> blocked_spine ms
      | MLet (IMeta _, _) -> true
      | MLet (m, _) -> blocked m
      | _ -> false
    in
    blocked m
  in
  match eqn with
  | EqualSort (s1, s2) -> (
    if eq_sort s1 s2 then
      []
    else
      match (s1, s2) with
      | SMeta (x, _), SMeta (y, _) when SMeta.compare x y < 0 ->
        [ EqualSort (s1, s2) ]
      | SMeta (x, _), SMeta (y, _) when SMeta.compare x y > 0 ->
        [ EqualSort (s2, s1) ]
      | SMeta (x, _), SMeta (y, _) when SMeta.compare x y = 0 -> []
      | _, SMeta _ -> [ EqualSort (s1, s2) ]
      | SMeta _, _ -> [ EqualSort (s2, s1) ]
      | _ -> failwith "unifier1.simpl_iprbm(EqualSort)")
  | EqualTerm (env, m1, m2) -> (
    let m1 = whnf ~expand env m1 in
    let m2 = whnf ~expand env m2 in
    Debug.exec (fun () ->
        pr "@[simpl_tm ~expand:%b(@;<1 2>%a,@;<1 2>%a)@]@." expand pp_tm m1
          pp_tm m2);
    match (m1, m2) with
    (* inference *)
    | IMeta (x, _, _), IMeta (y, _, _) when IMeta.compare x y < 0 ->
      [ EqualTerm (env, m1, m2) ]
    | IMeta (x, _, _), IMeta (y, _, _) when IMeta.compare x y > 0 ->
      [ EqualTerm (env, m2, m1) ]
    | IMeta (x, _, _), IMeta (y, _, _) when IMeta.compare x y = 0 -> []
    | _, IMeta _ -> [ EqualTerm (env, m1, m2) ]
    | IMeta _, _ -> [ EqualTerm (env, m2, m1) ]
    | PMeta x1, PMeta x2 when eq_vars x1 x2 -> []
    (* core *)
    | Type s1, Type s2 -> simpl_iprbm (EqualSort (s1, s2))
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Const (x1, ss1), Const (x2, ss2) when Const.equal x1 x2 ->
      List.concat
        (List.map2 (fun s1 s2 -> simpl_iprbm (EqualSort (s1, s2))) ss1 ss2)
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) when relv1 = relv2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns0 = simpl_iprbm (EqualSort (s1, s2)) in
      let eqns1 = simpl_iprbm (EqualTerm (env, a1, a2)) in
      let eqns2 = simpl_iprbm (EqualTerm (env, b1, b2)) in
      eqns0 @ eqns1 @ eqns2
    | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
      Debug.exec (fun () ->
          pr "@[simpl_function(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm m1 pp_tm m2);
      let _, cls1, cls2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_iprbm (EqualTerm (env, a1, a2)) in
      let eqns2 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 -> simpl_iprbm (EqualTerm (env, rhs1, rhs2))
            | None, None -> []
            | _ -> failwith "unifier.simpl_iprbm(Fun)")
          cls1 cls2
      in
      eqns1 @ List.concat eqns2
    | _, App _
    | App _, _ -> (
      try
        let hd1, sp1 = unApps m1 in
        let hd2, sp2 = unApps m2 in
        let eqns1 = simpl_iprbm (EqualTerm (env, hd1, hd2)) in
        let eqns2 =
          List.map2 (fun m n -> simpl_iprbm (EqualTerm (env, m, n))) sp1 sp2
        in
        eqns1 @ List.concat eqns2
      with
      | _ when not expand -> simpl_iprbm ~expand:true (EqualTerm (env, m1, m2))
      | _ when imeta_blocked m1 || imeta_blocked m2 -> [ eqn ]
      | _ ->
        failwith "@[<v 0>unifier1.simpl_iprbm(@;<1 2>%a,@;<1 2>%a@;<1 0>)@]"
          pp_tm m1 pp_tm m2)
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) when relv1 = relv2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_iprbm (EqualTerm (env, m1, m2)) in
      let eqns2 = simpl_iprbm (EqualTerm (env, n1, n2)) in
      eqns1 @ eqns2
    (* inductive *)
    | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2) when Ind.equal d1 d2 ->
      let eqns0 =
        List.map2 (fun s1 s2 -> simpl_iprbm (EqualSort (s1, s2))) ss1 ss2
      in
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_iprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 =
        List.map2 (fun n1 n2 -> simpl_iprbm (EqualTerm (env, n1, n2))) ns1 ns2
      in
      List.concat eqns0 @ List.concat eqns1 @ List.concat eqns2
    | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2)
      when Constr.equal c1 c2 ->
      let eqns0 =
        List.map2 (fun s1 s2 -> simpl_iprbm (EqualSort (s1, s2))) ss1 ss2
      in
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_iprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 =
        List.map2 (fun n1 n2 -> simpl_iprbm (EqualTerm (env, n1, n2))) ns1 ns2
      in
      List.concat eqns0 @ List.concat eqns1 @ List.concat eqns2
    | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_iprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 = simpl_iprbm (EqualTerm (env, a1, a2)) in
      let eqns3 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 -> simpl_iprbm (EqualTerm (env, rhs1, rhs2))
            | None, None -> []
            | _ -> failwith "unifier.simpl_iprbm(Match)")
          cls1 cls2
      in
      List.concat eqns1 @ eqns2 @ List.concat eqns3
    (* monad *)
    | IO a1, IO a2 -> simpl_iprbm (EqualTerm (env, a1, a2))
    | Return m1, Return m2 -> simpl_iprbm (EqualTerm (env, m1, m2))
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_iprbm (EqualTerm (env, m1, m2)) in
      let eqns2 = simpl_iprbm (EqualTerm (env, n1, n2)) in
      eqns1 @ eqns2
    (* magic *)
    | Magic a1, Magic a2 -> simpl_iprbm (EqualTerm (env, a1, a2))
    | _ when not expand -> simpl_iprbm ~expand:true (EqualTerm (env, m1, m2))
    | _ when imeta_blocked m1 || imeta_blocked m2 -> [ eqn ]
    | _ ->
      failwith "@[<v 0>unifier1.simpl_iprbm(@;<1 2>%a,@;<1 2>%a@;<1 0>)@]" pp_tm
        m1 pp_tm m2)

let solve_iprbm ((smeta_map, imeta_map) : meta_map) (eqn : IPrbm.eqn) =
  let open IPrbm in
  let svar_spine sp =
    List.map
      (function
        | SVar x -> x
        | _ -> SVar.mk "")
      sp
  in
  let var_spine sp =
    List.map
      (function
        | PMeta x -> x
        | Var x -> x
        | _ -> Var.mk "")
      sp
  in
  match eqn with
  | EqualSort (s1, s2) -> (
    match (s1, s2) with
    | _, SMeta (x, xs) ->
      if occurs_sort x s1 then
        (smeta_map, imeta_map, None)
      else
        let xs = svar_spine xs in
        let bnd = bind_mvar (Array.of_list xs) (lift_sort s1) in
        (SMeta.Map.add x (unbox bnd) smeta_map, imeta_map, None)
    | _ -> (smeta_map, imeta_map, Some eqn))
  | EqualTerm (env, m1, m2) -> (
    match (m1, m2) with
    | _, IMeta (x, ss, xs) ->
      if occurs_tm x m1 then
        (smeta_map, imeta_map, None)
      else
        let ss = svar_spine ss in
        let xs = var_spine xs in
        let bnd = bind_mvar (Array.of_list xs) (lift_tm m1) in
        let bnd = bind_mvar (Array.of_list ss) bnd in
        (smeta_map, IMeta.Map.add x (unbox bnd) imeta_map, None)
    | _ -> (smeta_map, imeta_map, Some eqn))

let unify_iprbm meta_map (eqns : IPrbm.eqns) =
  let open IPrbm in
  let rec aux_eqns ((smeta_map, imeta_map) as meta_map) delay = function
    | [] -> (meta_map, delay)
    | EqualSort (s1, s2) :: eqns -> (
      let s1 = resolve_sort smeta_map s1 in
      let s2 = resolve_sort smeta_map s2 in
      match simpl_iprbm (EqualSort (s1, s2)) with
      | [] -> aux_eqns meta_map delay eqns
      | eqn :: eqns0 -> (
        let smeta_map, imeta_map, eqn_opt = solve_iprbm meta_map eqn in
        match eqn_opt with
        | Some eqn ->
          aux_eqns (smeta_map, imeta_map) (eqn :: delay) (eqns0 @ eqns)
        | None -> aux_eqns (smeta_map, imeta_map) delay (eqns0 @ eqns)))
    | EqualTerm (env, m1, m2) :: eqns -> (
      let m1 = resolve_tm meta_map m1 in
      let m2 = resolve_tm meta_map m2 in
      match simpl_iprbm (EqualTerm (env, m1, m2)) with
      | [] -> aux_eqns meta_map delay eqns
      | eqn :: eqns0 -> (
        let smeta_map, imeta_map, eqn_opt = solve_iprbm meta_map eqn in
        match eqn_opt with
        | Some eqn ->
          aux_eqns (smeta_map, imeta_map) (eqn :: delay) (eqns0 @ eqns)
        | None -> aux_eqns (smeta_map, imeta_map) delay (eqns0 @ eqns)))
  in
  aux_eqns meta_map [] eqns

let rec simpl_pprbm ?(expand = false) eqn =
  let open PPrbm in
  match eqn with
  | EqualPat _ -> failwith "unifier1.simpl_pprbm(EqualPat)"
  | EqualTerm (env, m1, m2) -> (
    let m1 = whnf ~expand env m1 in
    let m2 = whnf ~expand env m2 in
    Debug.exec (fun () ->
        pr "@[simpl_pprbm ~expand:%b(@;<1 2>%a,@;<1 2>%a)@]@." expand pp_tm m1
          pp_tm m2);
    match (m1, m2) with
    (* inference *)
    | IMeta (x1, _, _), IMeta (x2, _, _) when IMeta.equal x2 x2 -> []
    | PMeta x, PMeta y when compare_vars x y < 0 -> [ EqualTerm (env, m1, m2) ]
    | PMeta x, PMeta y when compare_vars x y > 0 -> [ EqualTerm (env, m2, m1) ]
    | PMeta x, PMeta y when compare_vars x y = 0 -> []
    | _, PMeta _ -> [ EqualTerm (env, m1, m2) ]
    | PMeta _, _ -> [ EqualTerm (env, m2, m1) ]
    (* core *)
    | Type s1, Type s2 when eq_sort s1 s2 -> []
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Const (x1, ss1), Const (x2, ss2)
      when Const.equal x1 x2 && List.equal eq_sort ss1 ss2 ->
      []
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2)
      when relv1 = relv2 && eq_sort s1 s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, a1, a2)) in
      let eqns2 = simpl_pprbm (EqualTerm (env, b1, b2)) in
      eqns1 @ eqns2
    | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
      let _, cls1, cls2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, a1, a2)) in
      let eqns2 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 -> simpl_pprbm (EqualTerm (env, rhs1, rhs2))
            | _ -> [])
          cls1 cls2
      in
      eqns1 @ List.concat eqns2
    | _, App _
    | App _, _ -> (
      try
        let hd1, sp1 = unApps m1 in
        let hd2, sp2 = unApps m2 in
        let eqns1 = simpl_pprbm (EqualTerm (env, hd1, hd2)) in
        let eqns2 =
          List.map2 (fun m n -> simpl_pprbm (EqualTerm (env, m, n))) sp1 sp2
        in
        eqns1 @ List.concat eqns2
      with
      | _ when expand -> []
      | _ -> simpl_pprbm ~expand:true (EqualTerm (env, m1, m2)))
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) when relv1 = relv2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, m1, m2)) in
      let eqns2 = simpl_pprbm (EqualTerm (env, n1, n2)) in
      eqns1 @ eqns2
    (* inductive *)
    | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2)
      when Ind.equal d1 d2 && List.equal eq_sort ss1 ss2 ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_pprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 =
        List.map2 (fun n1 n2 -> simpl_pprbm (EqualTerm (env, n1, n2))) ns1 ns2
      in
      List.concat eqns1 @ List.concat eqns2
    | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2)
      when Constr.equal c1 c2 && List.equal eq_sort ss1 ss2 ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_pprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 =
        List.map2 (fun n1 n2 -> simpl_pprbm (EqualTerm (env, n1, n2))) ns1 ns2
      in
      List.concat eqns1 @ List.concat eqns2
    | Constr (c1, _, _, _), Constr (c2, _, _, _) when not (Constr.equal c1 c2)
      ->
      failwith "unifier.simpl_pprbm(Constr(%a, %a))" Constr.pp c1 Constr.pp c2
    | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_pprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 = simpl_pprbm (EqualTerm (env, a1, a2)) in
      let eqns3 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 -> simpl_pprbm (EqualTerm (env, rhs1, rhs2))
            | _ -> [])
          cls1 cls2
      in
      List.concat eqns1 @ eqns2 @ List.concat eqns3
    (* monad *)
    | IO a1, IO a2 -> simpl_pprbm (EqualTerm (env, a1, a2))
    | Return m1, Return m2 -> simpl_pprbm (EqualTerm (env, m1, m2))
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, m1, m2)) in
      let eqns2 = simpl_pprbm (EqualTerm (env, n1, n2)) in
      eqns1 @ eqns2
    (* magic *)
    | Magic a1, Magic a2 -> simpl_pprbm (EqualTerm (env, a1, a2))
    | _ when not expand -> simpl_pprbm ~expand:true (EqualTerm (env, m1, m2))
    | _ -> [])

let solve_pprbm map eqn =
  let open PPrbm in
  match eqn with
  | EqualTerm (_, m, PMeta x) ->
    if occur x (lift_tm (demote_pmeta m)) then
      map
    else
      Var.Map.add x m map
  | _ -> failwith "unifier1.solve_pprbm(solve)"

let unify_pprbm local global =
  let open PPrbm in
  Debug.exec (fun () ->
      pr "@[unify_local(@;<1 2>@[%a@]@;<1 0>)@]@." pp_eqns local);
  Debug.exec (fun () ->
      pr "@[unify_global(@;<1 2>@[%a@]@;<1 0>)@]@." pp_eqns global);
  let rec aux_eqns var_map = function
    | [] -> var_map
    | EqualPat (env, m, PVar x, _) :: eqns -> (
      let m = subst_pmeta var_map m in
      let n = subst_pmeta var_map (PMeta x) in
      match simpl_pprbm (EqualTerm (env, m, n)) with
      | [] -> aux_eqns var_map eqns
      | eqn :: eqns0 ->
        let var_map = solve_pprbm var_map eqn in
        aux_eqns var_map (eqns0 @ eqns))
    | EqualPat _ :: eqns -> failwith "unifier1e.unify_pprbm"
    | EqualTerm (env, m, n) :: eqns -> (
      let m = subst_pmeta var_map m in
      let n = subst_pmeta var_map n in
      match simpl_pprbm (EqualTerm (env, m, n)) with
      | [] -> aux_eqns var_map eqns
      | eqn :: eqns0 ->
        let var_map = solve_pprbm var_map eqn in
        aux_eqns var_map (eqns0 @ eqns))
  and flatten_eqn = function
    | EqualPat (env, m, PVar x, _) -> EqualTerm (env, m, PMeta x)
    | EqualPat _ -> failwith "unifier1e.solve_pprbm(unify)"
    | eqn -> eqn
  in
  let local = List.map flatten_eqn local in
  let local_map = aux_eqns Var.Map.empty local in
  Debug.exec (fun () -> pr "local_map solved@.");
  let global = List.map flatten_eqn global in
  let global_map = aux_eqns local_map global in
  Debug.exec (fun () -> pr "global_map solved@.");
  (local_map, global_map)

let succeed_pprbm global =
  try
    let _ = unify_pprbm [] global in
    true
  with
  | _ -> false
