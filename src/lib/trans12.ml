open Fmt
open Bindlib
open Names
open Syntax1
open Context12
open Constraint12
open Equality12
open Unifier12
open Pprint1

module State : sig
  open Resolver

  val add_const : Const.t -> Const.t RMap.t -> unit
  val add_ind : Ind.t -> sorts -> Ind.t -> unit
  val add_constr : Constr.t -> sorts -> Constr.t -> unit
  val find_const : Const.t -> sorts -> Const.t
  val find_ind : Ind.t -> sorts -> Ind.t
  val find_constr : Constr.t -> sorts -> Constr.t
end = struct
  let state = ref Resolver.empty
  let add_const x0 rmap = state := Resolver.add_const x0 rmap !state
  let add_ind d0 ss d1 = state := Resolver.add_ind d0 ss d1 !state
  let add_constr c0 ss c1 = state := Resolver.add_constr c0 ss c1 !state
  let find_const x0 ss = Resolver.find_const x0 ss !state
  let find_ind d0 ss = Resolver.find_ind d0 ss !state
  let find_constr c0 ss = Resolver.find_constr c0 ss !state
end

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

module Logical = struct
  let assert_sort = function
    | U -> ()
    | L -> ()
    | _ -> failwith "trans12.Logical.assert_sort"

  let assert_equal env m n =
    if not (eq_tm env m n) then failwith "trans12.Logical.assert_equal(%a, %a)" pp_tm m pp_tm n

  let rec infer_sort ctx env a =
    let t = infer_tm ctx env a in
    match whnf env t with
    | Type U -> U
    | Type L -> L
    | _ -> failwith "trans12.Logical.infer_sort(%a : %a)" pp_tm a pp_tm t

  and infer_tm ctx env m : tm =
    match m with
    (* inference *)
    | Ann (m, a) ->
      let _ = infer_sort ctx env a in
      check_tm ctx env m a;
      a
    | IMeta _ -> failwith "trans12.Logical.infer_tm(IMeta)"
    | PMeta x -> fst (Ctx.find_var x ctx)
    (* core *)
    | Type s ->
      assert_sort s;
      Type U
    | Var x -> fst (Ctx.find_var x ctx)
    | Const (x0, ss) ->
      let x1 = State.find_const x0 ss in
      fst (Ctx.find_const x1 ctx)
    | Pi (_, s, a, bnd) ->
      assert_sort s;
      let x, b = unbind bnd in
      let t = infer_sort ctx env a in
      let _ = infer_sort (Ctx.add_var x a t ctx) env b in
      Type s
    | Fun (a, bnd) ->
      let x, cls = unbind bnd in
      let s = infer_sort ctx env a in
      check_cls (Ctx.add_var x a s ctx) env cls a;
      a
    | App (m, n) -> (
      let t = infer_tm ctx env m in
      match whnf env t with
      | Pi (_, _, a, bnd) ->
        check_tm ctx env n a;
        subst bnd n
      | _ -> failwith "trans12.Logical.infer_tm(App)")
    | Let (_, m, bnd) ->
      let x, n = unbind bnd in
      let a = infer_tm ctx env m in
      let s = infer_sort ctx env a in
      infer_tm (Ctx.add_var x a s ctx) (Env.add_var x m env) n
    (* inductive *)
    | Ind (d0, ss, ms, ns) ->
      List.iter assert_sort ss;
      let d1 = State.find_ind d0 ss in
      let ptl, _ = Ctx.find_ind d1 ctx in
      infer_ptl ctx env ms ns ptl
    | Constr (c0, ss, ms, ns) ->
      List.iter assert_sort ss;
      let c1 = State.find_constr c0 ss in
      let ptl, _, _ = Ctx.find_constr c1 ctx in
      infer_ptl ctx env ms ns ptl
    | Match (ms, a, cls) ->
      let b = infer_motive ctx env ms a in
      check_cls ctx env cls a;
      b
    (* monad *)
    | IO a ->
      let _ = infer_sort ctx env a in
      Type L
    | Return m -> IO (infer_tm ctx env m)
    | MLet (m, bnd) -> (
      let t1 = infer_tm ctx env m in
      match whnf env t1 with
      | IO a -> (
        let s = infer_sort ctx env a in
        let x, n = unbind bnd in
        let t2 = infer_tm (Ctx.add_var x a s ctx) env n in
        match whnf env t2 with
        | IO b -> IO b
        | _ -> failwith "trans12.Logical.infer_tm(MLet)")
      | _ -> failwith "trans12.Logical.infer_tm(MLet)")
    (* magic *)
    | Magic a ->
      let _ = infer_sort ctx env a in
      a

  and infer_ptl ctx env ms ns ptl =
    let rec aux_param ms ptl =
      match (ms, ptl) with
      | [], PBase tl -> aux_tele ns tl
      | m :: ms, PBind (a, bnd) ->
        check_tm ctx env m a;
        aux_param ms (subst bnd m)
      | _ -> failwith "trans12.Logical.infer_ptl(param)"
    and aux_tele ns tl =
      match (ns, tl) with
      | [], TBase a -> a
      | n :: ns, TBind (_, a, bnd) ->
        check_tm ctx env n a;
        aux_tele ns (subst bnd n)
      | _ -> failwith "trans12.Logical.infer_ptl(tele)"
    in
    aux_param ms ptl

  and infer_motive ctx env ms a =
    match (ms, whnf env a) with
    | [], a -> a
    | m :: ms, Pi (_, _, a, bnd) ->
      check_tm ctx env m a;
      infer_motive ctx env ms (subst bnd m)
    | _ -> failwith "trans12.Logical.infer_motive"

  and check_tm ctx env m a =
    match m with
    | Fun (b, bnd) ->
      let x, cls = unbind bnd in
      let s = infer_sort ctx env b in
      assert_equal env a b;
      check_cls (Ctx.add_var x a s ctx) env cls a
    | _ ->
      let b = infer_tm ctx env m in
      assert_equal env a b

  and check_cls ctx env cls a : unit =
    let rec is_absurd eqns rhs =
      match (eqns, rhs) with
      | PPrbm.EqualPat (_, _, PMeta _, PAbsurd, _) :: _, None -> true
      | PPrbm.EqualPat (_, _, PMeta _, PAbsurd, _) :: _, Some _ ->
        failwith "trans12.Logical.is_absurd"
      | _ :: eqns, _ -> is_absurd eqns rhs
      | [], _ -> false
    in
    let rec get_absurd = function
      | PPrbm.EqualPat (_, _, PMeta _, PAbsurd, a) :: _ -> a
      | _ :: eqns -> get_absurd eqns
      | [] -> failwith "trans12.Logical.get_absurd"
    in
    let rec can_split = function
      | PPrbm.EqualPat (_, _, PMeta _, PMul _, _) :: _ -> true
      | PPrbm.EqualPat (_, _, PMeta _, PAdd _, _) :: _ -> true
      | _ :: eqns -> can_split eqns
      | [] -> false
    in
    let rec first_split = function
      | PPrbm.EqualPat (_, _, PMeta x, PMul _, a) :: _ -> (x, a)
      | PPrbm.EqualPat (_, _, PMeta x, PAdd _, a) :: _ -> (x, a)
      | _ :: eqns -> first_split eqns
      | [] -> failwith "trans1e.Logical.first_split"
    in
    let fail_on_ind global ctx env d1 ss ms a =
      let _, cs0 = Ctx.find_ind d1 ctx in
      List.iter
        (fun c0 ->
          let c1 = State.find_constr c0 ss in
          let param, _, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          let _, t = unbind_tele tele in
          let global = PPrbm.EqualTerm (env, a, t) :: global in
          if not (has_failed (fun () -> unify_pprbm global)) then
            failwith "trans12.Logical.fail_on_ind")
        cs0
    in
    let rec aux_prbm ctx env (prbm : PPrbm.t) a =
      match prbm.clause with
      (* empty *)
      | [] -> (
        if not (has_failed (fun () -> unify_pprbm prbm.global)) then
          match whnf env a with
          | Pi (_, _, a, _) -> (
            match whnf env a with
            | Ind (d0, ss, ms, ns) ->
              let d1 = State.find_ind d0 ss in
              fail_on_ind prbm.global ctx env d1 ss ms a
            | _ -> failwith "trans12.Logical.check_cls(Empty)")
          | _ -> failwith "trans12.Logical.check_cls(Empty)")
      (* case intro *)
      | (eqns, p :: ps, rhs) :: clause -> (
        match whnf env a with
        | Pi (relv, _, a, bnd) ->
          let x, b = unbind_pmeta bnd in
          let s = infer_sort ctx env a in
          let ctx = Ctx.add_var x a s ctx in
          let prbm = prbm_add env prbm x a relv in
          aux_prbm ctx env prbm b
        | a -> failwith "trans12.Logical.check_cls(Intro(%a, %a))" pp_tm a (pp_ps " ") ps)
      (* case splitting *)
      | (eqns, [], rhs) :: _ when can_split eqns -> (
        let x, b = first_split eqns in
        match whnf env b with
        | Ind (d0, ss, ms, _) ->
          let d1 = State.find_ind d0 ss in
          let _, cs0 = Ctx.find_ind d1 ctx in
          List.iter
            (fun c0 ->
              let c1 = State.find_constr c0 ss in
              let param, _, _ = Ctx.find_constr c1 ctx in
              let tele = param_inst param ms in
              let args, t = unbind_tele tele in
              let ctx =
                List.fold_left
                  (fun acc (_, x, a) ->
                    let s = infer_sort ctx env a in
                    Ctx.add_var x a s acc)
                  ctx args
              in
              let m = Constr (c0, ss, ms, List.map (fun (_, x, _) -> PMeta x) args) in
              let var_map = Var.Map.singleton x m in
              let a = subst_pmeta var_map a in
              let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
              let prbm = prbm_simpl ctx env var_map prbm in
              let prbm = PPrbm.{ prbm with global = EqualTerm (env, b, t) :: prbm.global } in
              aux_prbm ctx env prbm a)
            cs0
        | _ -> failwith "trans12.Logical.check_cls(Split)")
      (* absurd pattern *)
      | (eqns, [], rhs) :: _ when is_absurd eqns rhs -> (
        if not (has_failed (fun () -> unify_pprbm prbm.global)) then
          let a = get_absurd eqns in
          match whnf env a with
          | Ind (d0, ss, ms, ns) ->
            let d1 = State.find_ind d0 ss in
            fail_on_ind prbm.global ctx env d1 ss ms a
          | _ -> failwith "trans12.Logical.check_cls(Absurd)")
      (* case coverage *)
      | (eqns, [], rhs) :: _ -> (
        match rhs with
        | Some m ->
          let var_map = unify_pprbm (prbm.global @ eqns) in
          let a = resolve_pmeta var_map a in
          let ctx = Ctx.map_var (resolve_pmeta var_map) ctx in
          let rhs = resolve_pmeta var_map m in
          check_tm ctx env rhs a
        | None ->
          if not (has_failed (fun () -> unify_pprbm prbm.global)) then
            failwith "trans12.Logical.check_cls(Cover)")
    in
    aux_prbm ctx env (PPrbm.of_cls cls) a

  and prbm_add env prbm x a relv =
    match prbm.clause with
    | [] -> prbm
    | (eqns, p :: ps, rhs) :: clause ->
      let prbm = prbm_add env { prbm with clause } x a relv in
      let clause = (eqns @ [ PPrbm.EqualPat (relv, env, PMeta x, p, a) ], ps, rhs) :: prbm.clause in
      { prbm with clause }
    | _ -> failwith "trans12.Logical.prbm_add"

  and prbm_simpl ctx env var_map prbm =
    let rec aux_global = function
      | [] -> []
      | PPrbm.EqualTerm (env, a, b) :: eqns ->
        let a = subst_pmeta var_map a in
        let b = subst_pmeta var_map b in
        let eqns = aux_global eqns in
        PPrbm.EqualTerm (env, a, b) :: eqns
      | PPrbm.EqualPat _ :: _ -> failwith "trans12.Logical.prbm_simpl(Global)"
    in
    let rec aux_clause = function
      | [] -> []
      | (eqns, ps, rhs) :: clause -> (
        let clause = aux_clause clause in
        let opt =
          List.fold_left
            (fun acc eqn ->
              match (acc, eqn) with
              | Some acc, PPrbm.EqualPat (relv, env, l, r, a) -> (
                let l = subst_pmeta var_map l in
                let a = subst_pmeta var_map a in
                match p_simpl relv ctx env l r a with
                | Some eqns -> Some (acc @ eqns)
                | None -> None)
              | _ -> None)
            (Some []) eqns
        in
        match opt with
        | Some eqns -> (eqns, ps, rhs) :: clause
        | None -> clause)
    in
    let global = aux_global prbm.global in
    let clause = aux_clause prbm.clause in
    { global; clause }

  and p_simpl relv ctx env m p a =
    let a = whnf env a in
    match (m, p, a) with
    (* simplify multiplicative pattern *)
    | Constr (c0, _, _, ns), PMul (c, ps), Ind (d0, ss, ms, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        if Constr.equal c0 c then
          let c1 = State.find_constr c0 ss in
          let param, _, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          ps_simpl relv ctx env ns ps tele
        else
          None
      else
        failwith "trans12.Logical.p_simpl(PMul)"
    (* simplify additive pattern *)
    | Constr (c0, _, _, ns), PAdd (c, i, ps), Ind (d0, ss, ms, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        if Constr.equal c0 c then
          let c1 = State.find_constr c0 ss in
          let param, _, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          ps_simpl relv ctx env ns ps tele
        else
          None
      else
        failwith "trans12.Logical.p_simpl(PAdd)"
    (* fully simplified pattern *)
    | Constr _, _, Ind _ -> Some [ PPrbm.EqualPat (relv, env, m, p, a) ]
    (* blocked multiplicative pattern *)
    | _, PMul (c, _), Ind (d0, ss, _, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        Some [ PPrbm.EqualPat (relv, env, m, p, a) ]
      else
        failwith "trans12.Logical.p_simpl(PMul)"
    (* blocked additive pattern *)
    | _, PAdd (c, _, _), Ind (d0, ss, _, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        Some [ PPrbm.EqualPat (relv, env, m, p, a) ]
      else
        failwith "trans12.Logical.p_simpl(PMul)"
    | m, p, a -> Some [ PPrbm.EqualPat (relv, env, m, p, a) ]

  and ps_simpl relv0 ctx env ms ps tele =
    match (relv0, ms, ps, tele) with
    | R, m :: ms, p :: ps, TBind (relv, a, bnd) -> (
      let opt1 = p_simpl relv ctx env m p a in
      let tele = subst bnd m in
      let opt2 = ps_simpl relv0 ctx env ms ps tele in
      match (opt1, opt2) with
      | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
      | _ -> None)
    (* sub-patterns inherit irrelevancy *)
    | N, m :: ms, p :: ps, TBind (_, a, bnd) -> (
      let opt1 = p_simpl N ctx env m p a in
      let tele = subst bnd m in
      let opt2 = ps_simpl N ctx env ms ps tele in
      match (opt1, opt2) with
      | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
      | _ -> None)
    | _, [], [], TBase _ -> Some []
    | _ -> None
end

module Program = struct
  let trans_sort = function
    | U -> Syntax2.U
    | L -> Syntax2.L
    | _ -> failwith "trans12.Program.trans_sort"

  let trans_relv = function
    | N -> Syntax2.N
    | R -> Syntax2.R

  let trans_var x = Syntax2.(copy_var x var (name_of x))
  let trans_mvar xs = Array.map trans_var xs

  let rec infer_tm ctx env m =
    match m with
    (* inference *)
    | Ann (m, a) ->
      let _ = Logical.infer_sort ctx env a in
      let m_elab, usg = check_tm ctx env m a in
      (a, m_elab, usg)
    | IMeta _ -> failwith "trans12.Program.infer_tm(IMeta)"
    | PMeta x ->
      let a, s = Ctx.find_var x ctx in
      Syntax2.(a, _Var (trans_var x), Usage.var_singleton x (s, false))
    (* core *)
    | Type _ -> failwith "trans12.Program.infer_tm(Type)"
    | Var x ->
      let a, s = Ctx.find_var x ctx in
      Syntax2.(a, _Var (trans_var x), Usage.var_singleton x (s, false))
    | Const (x0, ss) ->
      let x1 = State.find_const x0 ss in
      let a, s = Ctx.find_const x1 ctx in
      Syntax2.(a, _Const x1, Usage.const_singleton x1 (s, false))
    | Pi _ -> failwith "trans12.Program.infer_tm(Pi)"
    | Fun (a, bnd) ->
      let x, cls = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      let cls_elab, usg = check_cls (Ctx.add_var x a s ctx) env cls a in
      let usg =
        match s with
        | U ->
          let usg = Usage.remove_var x usg R U in
          Usage.refine_pure usg
        | L -> Usage.remove_var x usg N L
        | _ -> failwith "trans12.Program.infer_tm(Fun)"
      in
      Syntax2.(a, _Fun (bind_var (trans_var x) cls_elab), usg)
    | App (m, n) -> (
      let t, m_elab, usg1 = infer_tm ctx env m in
      match whnf env t with
      | Pi (N, s, a, bnd) ->
        Logical.check_tm ctx env n a;
        Syntax2.(subst bnd n, _App (trans_sort s) m_elab _Null, usg1)
      | Pi (R, s, a, bnd) ->
        let n_elab, usg2 = check_tm ctx env n a in
        Syntax2.(subst bnd n, _App (trans_sort s) m_elab n_elab, Usage.merge usg1 usg2)
      | _ -> failwith "trans12.Program.infer_tm(App)")
    | Let (N, m, bnd) ->
      let x, n = unbind bnd in
      let a = Logical.infer_tm ctx env m in
      let s = Logical.infer_sort ctx env a in
      let ctx = Ctx.add_var x a s ctx in
      let env = Env.add_var x m env in
      let b, n_elab, usg = infer_tm ctx env n in
      let usg = Usage.remove_var x usg N s in
      Syntax2.(b, _Let _Null (bind_var (trans_var x) n_elab), usg)
    | Let (R, m, bnd) ->
      let x, n = unbind bnd in
      let a, m_elab, usg1 = infer_tm ctx env m in
      let s = Logical.infer_sort ctx env a in
      let ctx = Ctx.add_var x a s ctx in
      let env = Env.add_var x m env in
      let b, n_elab, usg2 = infer_tm ctx env n in
      let usg = Usage.(merge usg1 (remove_var x usg2 R s)) in
      Syntax2.(b, _Let m_elab (bind_var (trans_var x) n_elab), usg)
    (* inductive *)
    | Ind _ -> failwith "trans12.Program.infer_tm(Ind)"
    | Constr (c0, ss, ms, ns) -> (
      List.iter Logical.assert_sort ss;
      let c1 = State.find_constr c0 ss in
      let ptl, relv, mode = Ctx.find_constr c1 ctx in
      let a, ns_elab, usg = infer_ptl ctx env ms ns ptl mode in
      let s = Logical.infer_sort ctx env a in
      match (s, relv, mode) with
      | _, R, M -> Syntax2.(a, _CMul c1 (box_list ns_elab), usg)
      | U, R, A ->
        let usg = Usage.refine_pure usg in
        Syntax2.(a, _CAdd c1 (box_list ns_elab), usg)
      | L, R, A -> Syntax2.(a, _CAdd c1 (box_list ns_elab), usg)
      | _ -> failwith "trans12.Program.infer_tm(Constr)")
    | Match (ms, a, cls) ->
      let b, ms_elab, usg1 = infer_motive ctx env ms a in
      let cls_elab, usg2 = check_cls ctx env cls a in
      Syntax2.(b, _Match (box_list ms_elab) cls_elab, Usage.merge usg1 usg2)
    | IO _ -> failwith "trans12.Program.infer_tm(IO)"
    | Return m ->
      let a, m_elab, usg = infer_tm ctx env m in
      Syntax2.(IO a, _Return m_elab, usg)
    | MLet (m, bnd) -> (
      let t1, m_elab, usg1 = infer_tm ctx env m in
      match whnf env t1 with
      | IO a -> (
        let s = Logical.infer_sort ctx env a in
        let x, n = unbind bnd in
        let t2, n_elab, usg2 = infer_tm (Ctx.add_var x a s ctx) env n in
        let usg = Usage.(merge usg1 (remove_var x usg2 R s)) in
        match whnf env t2 with
        | IO b -> Syntax2.(IO b, _MLet m_elab (bind_var (trans_var x) n_elab), usg)
        | _ -> failwith "trans12.Program.infer_tm(MLet)")
      | _ -> failwith "trans12.Program.infer_tm(MLet)")
    | Magic a ->
      let _ = Logical.infer_sort ctx env a in
      Syntax2.(a, _Magic, Usage.of_ctx ctx)

  and infer_ptl ctx env ms ns ptl mode =
    let rec aux_param ms ptl =
      match (ms, ptl) with
      | [], PBase tl -> (
        match mode with
        | M -> aux_M ns tl
        | A -> aux_A ns tl)
      | m :: ms, PBind (a, bnd) ->
        Logical.check_tm ctx env m a;
        aux_param ms (subst bnd m)
      | _ -> failwith "trans12.Program.infer_ptl(param)"
    and aux_M ns tl =
      match (ns, tl) with
      | [], TBase a -> (a, [], Usage.empty)
      | n :: ns, TBind (N, a, bnd) ->
        Logical.check_tm ctx env n a;
        let b, ns_elab, usg = aux_M ns (subst bnd n) in
        Syntax2.(b, _Null :: ns_elab, usg)
      | n :: ns, TBind (R, a, bnd) ->
        let n_elab, usg1 = check_tm ctx env n a in
        let b, ns_elab, usg2 = aux_M ns (subst bnd n) in
        Syntax2.(b, n_elab :: ns_elab, Usage.merge usg1 usg2)
      | _ -> failwith "trans12.Program.infer_ptl(multiplicative)"
    and aux_A ns tl =
      match (ns, tl) with
      | [], TBase a -> (a, [], Usage.of_ctx ctx)
      | n :: ns, TBind (N, a, bnd) ->
        Logical.check_tm ctx env n a;
        let b, ns_elab, usg = aux_A ns (subst bnd n) in
        Syntax2.(b, _Null :: ns_elab, usg)
      | n :: ns, TBind (R, a, bnd) ->
        let n_elab, usg1 = check_tm ctx env n a in
        let b, ns_elab, usg2 = aux_A ns (subst bnd n) in
        Syntax2.(b, n_elab :: ns_elab, Usage.refine_usage usg1 usg2)
      | _ -> failwith "trans12.Program.infer_ptl(additive)"
    in
    aux_param ms ptl

  and infer_motive ctx env ms a =
    match (ms, whnf env a) with
    | [], a -> (a, [], Usage.empty)
    | m :: ms, Pi (N, L, a, bnd) ->
      Logical.check_tm ctx env m a;
      let b, ms_elab, usg = infer_motive ctx env ms (subst bnd m) in
      Syntax2.(b, _Null :: ms_elab, usg)
    | m :: ms, Pi (R, L, a, bnd) ->
      let m_elab, usg1 = check_tm ctx env m a in
      let b, ms_elab, usg2 = infer_motive ctx env ms (subst bnd m) in
      Syntax2.(b, m_elab :: ms_elab, Usage.merge usg1 usg2)
    | _ -> failwith "trans12.Program.infer_motive"

  and check_tm ctx env m a =
    let b, m_elab, usg = infer_tm ctx env m in
    Logical.assert_equal env a b;
    (m_elab, usg)

  and check_cls ctx env cls a =
    let rec is_absurd eqns rhs =
      match (eqns, rhs) with
      | PPrbm.EqualPat (_, _, PMeta _, PAbsurd, _) :: _, None -> true
      | PPrbm.EqualPat (_, _, PMeta _, PAbsurd, _) :: _, Some _ ->
        failwith "trans12.Program.is_absurd"
      | _ :: eqns, _ -> is_absurd eqns rhs
      | [], _ -> false
    in
    let rec get_absurd = function
      | PPrbm.EqualPat (_, _, PMeta _, PAbsurd, a) :: _ -> a
      | _ :: eqns -> get_absurd eqns
      | [] -> failwith "trans12.Program.get_absurd"
    in
    let rec can_split = function
      | PPrbm.EqualPat (_, _, PMeta _, PMul _, _) :: _ -> true
      | PPrbm.EqualPat (_, _, PMeta _, PAdd _, _) :: _ -> true
      | _ :: eqns -> can_split eqns
      | [] -> false
    in
    let rec first_split = function
      | PPrbm.EqualPat (relv, _, PMeta x, PMul _, a) :: _ -> (relv, x, a)
      | PPrbm.EqualPat (relv, _, PMeta x, PAdd _, a) :: _ -> (relv, x, a)
      | _ :: eqns -> first_split eqns
      | [] -> failwith "trans12.Program.first_split"
    in
    let fail_on_ind global ctx env d1 ss ms a =
      let _, cs0 = Ctx.find_ind d1 ctx in
      List.iter
        (fun c0 ->
          let c1 = State.find_constr c0 ss in
          let param, _, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          let _, t = unbind_tele tele in
          let global = PPrbm.EqualTerm (env, a, t) :: global in
          if not (has_failed (fun () -> unify_pprbm global)) then
            failwith "trans12.Program.fail_on_ind")
        cs0;
      (Syntax2._Absurd, Usage.of_ctx ctx)
    in
    let rec aux_prbm ctx env (prbm : PPrbm.t) a =
      match prbm.clause with
      (* empty *)
      | [] -> (
        if has_failed (fun () -> unify_pprbm prbm.global) then
          (Syntax2._Absurd, Usage.of_ctx ctx)
        else
          match whnf env a with
          | Pi (_, _, a, _) -> (
            match whnf env a with
            | Ind (d0, ss, ms, ns) ->
              let d1 = State.find_ind d0 ss in
              fail_on_ind prbm.global ctx env d1 ss ms a
            | _ -> failwith "trans12.Program.check_cls(Empty)")
          | _ -> failwith "trans12.Program.check_cls(Empty)")
      (* case intro *)
      | (eqns, p :: ps, rhs) :: clause -> (
        match whnf env a with
        | Pi (relv, s, a, bnd) -> (
          let x, b = unbind_pmeta bnd in
          let t = Logical.infer_sort ctx env a in
          let ctx = Ctx.add_var x a s ctx in
          let prbm = prbm_add env prbm x a relv in
          let ctree, usg = aux_prbm ctx env prbm b in
          let usg = Usage.remove_var x usg relv t in
          match s with
          | U ->
            let usg = Usage.refine_pure usg in
            Syntax2.(_Lam (bind_var (trans_var x) ctree), usg)
          | L -> Syntax2.(_Lam (bind_var (trans_var x) ctree), usg)
          | _ -> failwith "trans12.Program.check_cls(Intro)")
        | a -> failwith "trans12.Program.check_cls(Intro(%a, %a))" pp_tm a (pp_ps " ") ps)
      (* case splitting *)
      | (eqns, [], rhs) :: _ when can_split eqns -> (
        let relv, x, b = first_split eqns in
        let s = Logical.infer_sort ctx env b in
        match whnf env b with
        | Ind (d0, ss, ms, _) ->
          let d1 = State.find_ind d0 ss in
          let _, cs0 = Ctx.find_ind d1 ctx in
          let cls_elab, usg =
            List.fold_left
              (fun (cls_elab, acc) c0 ->
                let c1 = State.find_constr c0 ss in
                let param, _, mode = Ctx.find_constr c1 ctx in
                let tele = param_inst param ms in
                let args, t = unbind_tele tele in
                let ctx, args =
                  List.fold_left_map
                    (fun acc (relv, x, a) ->
                      let s = Logical.infer_sort ctx env a in
                      (Ctx.add_var x a s acc, (x, s)))
                    ctx args
                in
                let m = Constr (c0, ss, ms, List.map (fun (x, _) -> PMeta x) args) in
                let var_map = Var.Map.singleton x m in
                let a = subst_pmeta var_map a in
                let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
                let prbm, relvs, i = prbm_simpl ctx env var_map prbm relv mode in
                let prbm = PPrbm.{ prbm with global = EqualTerm (env, b, t) :: prbm.global } in
                let ctree, usg = aux_prbm ctx env prbm a in
                let usg =
                  List.fold_left2
                    (fun acc (x, s) relv -> Usage.remove_var x acc relv s)
                    usg args relvs
                in
                let xs = List.map (fun (x, _) -> trans_var x) args in
                let cl_elab =
                  Syntax2.(
                    match mode with
                    | M -> _PMul c1 (bind_mvar (Array.of_list xs) ctree)
                    | A -> _PAdd c1 i (bind_mvar (Array.of_list xs) ctree))
                in
                (cl_elab :: cls_elab, Usage.refine_equal acc usg))
              ([], Usage.of_ctx ctx)
              cs0
          in
          let usg =
            match relv with
            | R -> Usage.add_var x s false usg
            | N -> usg
          in
          let cls_elab = box_list cls_elab in
          Syntax2.(_Case (trans_relv relv) (trans_sort s) (_Var (trans_var x)) cls_elab, usg)
        | _ -> failwith "trans12.Program.check_cls(split)")
      (* absurd pattern *)
      | (eqns, [], rhs) :: _ when is_absurd eqns rhs -> (
        if has_failed (fun () -> unify_pprbm prbm.global) then
          (Syntax2._Absurd, Usage.of_ctx ctx)
        else
          let a = get_absurd eqns in
          match whnf env a with
          | Ind (d0, ss, ms, ns) ->
            let d1 = State.find_ind d0 ss in
            fail_on_ind prbm.global ctx env d1 ss ms a
          | _ -> failwith "trans12.Program.check_cls(Absurd)")
      (* case coverage *)
      | (eqns, [], rhs) :: _ -> (
        match rhs with
        | Some m ->
          let var_map = unify_pprbm (prbm.global @ eqns) in
          let a = resolve_pmeta var_map a in
          let ctx = Ctx.map_var (resolve_pmeta var_map) ctx in
          let rhs = resolve_pmeta var_map m in
          check_tm ctx env rhs a
        | None ->
          if has_failed (fun () -> unify_pprbm prbm.global) then
            (Syntax2._Absurd, Usage.of_ctx ctx)
          else
            failwith "trans12.Program.check_cls(Cover)")
    in
    aux_prbm ctx env (PPrbm.of_cls cls) a

  and prbm_add env prbm x a relv =
    match prbm.clause with
    | [] -> prbm
    | (eqns, p :: ps, rhs) :: clause ->
      let prbm = prbm_add env { prbm with clause } x a relv in
      let clause = (eqns @ [ PPrbm.EqualPat (relv, env, PMeta x, p, a) ], ps, rhs) :: prbm.clause in
      { prbm with clause }
    | _ -> failwith "trans12.Program.prbm_add"
end
