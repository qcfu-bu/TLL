open Fmt
open Bindlib
open Names
open Syntax1
open Context12
open Constraint12
open Equality12
open Unifier12
open Pprint1
open Prelude1

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

module Logical = struct
  let assert_sort = function
    | U -> ()
    | L -> ()
    | _ -> failwith "trans12.Logical.assert_sort"

  let assert_equal env m n =
    Debug.exec (fun () -> pr "Logical.assert_equal(%a, %a)@." pp_tm m pp_tm n);
    if not (eq_tm env m n) then
      failwith "trans12.Logical.assert_equal(%a, %a)" pp_tm m pp_tm n

  let rec infer_sort ctx env a =
    let t = infer_tm ctx env a in
    match whnf env t with
    | Type U -> U
    | Type L -> L
    | _ -> failwith "trans12.Logical.assert_equal(%a : %a)" pp_tm a pp_tm t

  and infer_tm ctx env m =
    Debug.exec (fun () -> pr "@[Logical.infer_tm(%a)@]@." pp_tm m);
    match m with
    (* inference *)
    | Ann (m, a) ->
      let _ = infer_sort ctx env a in
      check_tm ctx env m a; a
    | IMeta _ -> failwith "trans12.Logical.infer_tm(IMeta)"
    | PMeta _ -> failwith "trans12.Logical.infer_tm(PMeta)"
    (* core *)
    | Type s ->
      assert_sort s; Type U
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
    | Fun (_, a, bnd) ->
      let x, cls = unbind bnd in
      let s = infer_sort ctx env a in
      check_cls (Ctx.add_var x a s ctx) env cls a; a
    | App (m, n) ->
      let t = infer_tm ctx env m in
      (match whnf env t with
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
      let ptl, _ = Ctx.find_constr c1 ctx in
      infer_ptl ctx env ms ns ptl
    | Match (_, ms, a, cls) ->
      let b = infer_motive ctx env ms a in
      check_cls ctx env cls a; b
    (* monad *)
    | IO a ->
      let _ = infer_sort ctx env a in
      Type L
    | Return m -> IO (infer_tm ctx env m)
    | MLet (m, bnd) ->
      let t1 = infer_tm ctx env m in
      (match whnf env t1 with
       | IO a ->
         let s = infer_sort ctx env a in
         let x, n = unbind bnd in
         let t2 = infer_tm (Ctx.add_var x a s ctx) env n in
         (match whnf env t2 with
          | IO b -> IO b
          | _ -> failwith "trans12.Logical.infer_tm(MLet)")
       | _ -> failwith "trans12.Logical.infer_tm(MLet)")
    (* primitive types *)
    | Int_t -> Type U
    | Char_t -> Type U
    | String_t -> Type U
    (* primitive terms *)
    | Int _ -> Int_t
    | Char _ -> Char_t 
    | String _ -> String_t
    (* primitive operators *)
    | Neg m -> check_tm ctx env m Int_t; Int_t
    | Add (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Int_t
    | Sub (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Int_t
    | Mul (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Int_t
    | Div (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Int_t
    | Mod (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Int_t
    | Lte (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Ind (bool_ind, [], [], [])
    | Gte (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Ind (bool_ind, [], [], [])
    | Lt (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Ind (bool_ind, [], [], [])
    | Gt (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Ind (bool_ind, [], [], [])
    | Eq (m, n) ->
      check_tm ctx env m Int_t;
      check_tm ctx env n Int_t;
      Ind (bool_ind, [], [], [])
    | Chr m -> check_tm ctx env m Int_t; Char_t
    | Ord m -> check_tm ctx env m Char_t; Int_t
    | Push (m, n) ->
      check_tm ctx env m String_t;
      check_tm ctx env n Char_t;
      String_t
    | Cat (m, n) ->
      check_tm ctx env m String_t;
      check_tm ctx env n String_t;
      String_t
    | Size m -> check_tm ctx env m String_t; Int_t
    | Indx (m, n) ->
      check_tm ctx env m String_t;
      check_tm ctx env n Int_t;
      Char_t
    (* primitive sessions *)
    | Proto -> Type U
    | Act (_, _, a, bnd) ->
      let x, b = unbind bnd in
      let s = infer_sort ctx env a in
      check_tm (Ctx.add_var x a s ctx) env b Proto;
      Proto
    | End -> Proto
    | Ch (_, a) -> check_tm ctx env a Proto; Type L
    (* primitive effects *)
    | Print m -> check_tm ctx env m String_t; IO (Ind (unit_ind, [], [], []))
    | Prerr m -> check_tm ctx env m String_t; IO (Ind (unit_ind, [], [], []))
    | ReadLn m -> check_tm ctx env m (Ind (unit_ind, [], [], [])); IO String_t
    | Fork m ->
      let t = infer_tm ctx env m in
      (match whnf env t with
       | Pi (R, L, a, bnd) ->
         (match whnf env a with
          | Ch (role, a) ->
            let _, b = unbind bnd in
            assert_equal env b (IO (Ind (unit_ind, [], [], [])));
            IO (Ch (not role, a))
          | _ -> failwith "trans12.Logical.infer_tm(Fork)")
       | _ -> failwith "trans12.Logical.infer_tm(Fork)")
    | Send m ->
      let t = infer_tm ctx env m in
      (match whnf env t with
       | Ch (role1, Act (relv, role2, a, bnd)) when role1 = role2 -> 
         let x, b = unbind bnd in
         let bnd = unbox (bind_var x (lift_tm (IO (Ch (role1, b))))) in
         Pi (relv, L, a, bnd)
       | _ -> failwith "trans12.Logical.infer_tm(Send)")
    | Recv m ->
      let t = infer_tm ctx env m in
      (match whnf env t with
       | Ch (role1, Act (relv, role2, a, bnd)) when role1 <> role2 ->
         let x, b = unbind bnd in
         let s = infer_sort ctx env a in
         let _b_t = _Pi R _U (lift_tm a) (bind_var x (_Type _L)) in
         let _b = _Lam _b_t x (_Ch role1 (lift_tm b)) in
         let ind = match relv with N -> exists0_ind | R -> exists1_ind in
         IO (Ind (ind, [s; L], [a; unbox _b], []))
       | _ -> failwith "trans12.Logical.infer_tm(Recv)")
    | Close m ->
      let t = infer_tm ctx env m in
      (match whnf env t with
       | Ch (_, End) -> IO (Ind (unit_ind, [], [], []))
       | _ -> failwith "trans12.Logical.infer_tm(Close)")
    (* magic *)
    | Magic a ->
      let _ = infer_sort ctx env a in a

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
    Debug.exec (fun () ->
        pr "@[Logical.check_tm(@;<1 2>@[%a@],@;<1 2>@[%a@]@;<1 0>)@]@." pp_tm m
          pp_tm a);
    let b = infer_tm ctx env m in
    assert_equal env a b

  and check_cls ctx env cls a =
    let infer_demote ctx env a =
      let ctx = Ctx.map_var demote_pmeta ctx in
      infer_sort ctx env (demote_pmeta a)
    in
    let rec is_absurd eqns rhs =
      match (eqns, rhs) with
      | EqualPat (_, _, PMeta _, PAbsurd, _) :: _, None -> true
      | EqualPat (_, _, PMeta _, PAbsurd, _) :: _, Some _ ->
        failwith "trans12.Logical.is_absurd"
      | _ :: eqns, _ -> is_absurd eqns rhs
      | [], _ -> false
    in
    let rec get_absurd = function
      | EqualPat (_, _, PMeta _, PAbsurd, a) :: _ -> a
      | _ :: eqns -> get_absurd eqns
      | [] -> failwith "trans12.Logical.get_absurd"
    in
    let rec can_split = function
      | EqualPat (_, _, PMeta _, PConstr _, _) :: _ -> true
      | _ :: eqns -> can_split eqns
      | [] -> false
    in
    let rec first_split = function
      | EqualPat (_, _, PMeta x, PConstr _, a) :: _ -> (x, a)
      | _ :: eqns -> first_split eqns
      | [] -> failwith "trans12.Logical.first_split"
    in
    let fail_on_ind global ctx d1 ss ms a =
      let _, cs0 = Ctx.find_ind d1 ctx in
      List.iter
        (fun c0 ->
           let c1 = State.find_constr c0 ss in
           let param, _ = Ctx.find_constr c1 ctx in
           let tele = param_inst param ms in
           let _, t = unbind_tele tele in
           let global = EqualTerm (env, a, t) :: global in
           if not (witness_distinct global) then
             failwith "trans12.Logical.fail_on_ind(%a)" Ind.pp d1)
        cs0
    in
    let rec aux_prbm ctx prbm a =
      match prbm.clause with
      (* empty *)
      | [] -> (
          Debug.exec (fun () -> pr "case_empty@.");
          if not (witness_distinct prbm.global) then
            match whnf env a with
            | Pi (_, _, a, _) -> (
                match whnf env a with
                | Ind (d0, ss, ms, ns) ->
                  let d1 = State.find_ind d0 ss in
                  fail_on_ind prbm.global ctx d1 ss ms a
                | _ -> failwith "trans12.Logical.check_cls(Empty)")
            | _ -> failwith "trans12.Logical.check_cls(Empty)")
      (* case intro *)
      | (eqns, p :: ps, rhs) :: clause -> (
          match whnf env a with
          | Pi (relv, _, a, bnd) ->
            let x, b = unbind_pmeta bnd in
            let s = infer_demote ctx env a in
            let ctx = Ctx.add_var x a s ctx in
            let prbm = prbm_add env prbm x a relv in
            aux_prbm ctx prbm b
          | a ->
            failwith "trans12.Logical.check_cls(Intro(%a, %a))" pp_tm a
              (pp_ps " ") ps)
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
                 let param, _ = Ctx.find_constr c1 ctx in
                 let tele = param_inst param ms in
                 let args, t = unbind_tele tele in
                 let ctx, ns =
                   List.fold_left_map
                     (fun ctx (_, x, a) ->
                        let s = infer_demote ctx env a in
                        (Ctx.add_var x a s ctx, PMeta x))
                     ctx args
                 in
                 let m = Constr (c0, ss, ms, ns) in
                 let var_map = Var.Map.singleton x m in
                 let a = subst_pmeta var_map a in
                 let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
                 let prbm = prbm_simpl ctx var_map prbm in
                 let prbm =
                   { prbm with global = EqualTerm (env, b, t) :: prbm.global }
                 in
                 aux_prbm ctx prbm a)
              cs0
          | _ -> failwith "trans12.Logical.check_cls(Split(%a))" pp_tm b)
      (* absurd pattern *)
      | (eqns, [], rhs) :: _ when is_absurd eqns rhs -> (
          Debug.exec (fun () -> pr "trans12.Logical.case_absurd@.");
          if not (witness_distinct prbm.global) then
            let a = get_absurd eqns in
            match whnf env a with
            | Ind (d0, ss, ms, ns) ->
              let d1 = State.find_ind d0 ss in
              fail_on_ind prbm.global ctx d1 ss ms a
            | _ -> failwith "trans12.Logical.check_cls(Absurd)")
      (* case coverage *)
      | (eqns, [], rhs) :: _ -> (
          Debug.exec (fun () ->
              pr "@[<v 0>case_coverage{|@;<1 2>%a@;<1 0>|}@]@." pp_pprbm prbm);
          match rhs with
          | Some rhs ->
            let local_map, global_map = unify_pprbm eqns prbm.global in
            let a = resolve_pmeta global_map a in
            let ctx = Ctx.map_var (resolve_pmeta global_map) ctx in
            let env = Env.merge_var (Var.Map.map demote_pmeta global_map) env in
            let rhs = resolve_pmeta local_map rhs in
            Debug.exec (fun () ->
                pr "@[case_coverage_ok(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm rhs pp_tm a);
            check_tm ctx env rhs a
          | None ->
            if not (witness_distinct prbm.global) then
              failwith "trans12.Logical.check_cls(Cover)")
    in
    aux_prbm ctx (of_cls cls) a

  and prbm_add env prbm x a relv =
    match prbm.clause with
    | [] -> prbm
    | (eqns, p :: ps, rhs) :: clause ->
      let prbm = prbm_add env { prbm with clause } x a relv in
      let clause =
        (eqns @ [ EqualPat (relv, env, PMeta x, p, a) ], ps, rhs) :: prbm.clause
      in
      { prbm with clause }
    | _ -> failwith "trans12.Logical.prbm_add"

  and prbm_simpl ctx var_map prbm =
    let rec aux_global = function
      | [] -> []
      | EqualTerm (env, a, b) :: eqns ->
        let a = subst_pmeta var_map a in
        let b = subst_pmeta var_map b in
        let eqns = aux_global eqns in
        EqualTerm (env, a, b) :: eqns
      | EqualPat _ :: _ -> failwith "trans12.Logical.prbm_simpl(Global)"
    in
    let rec aux_clause = function
      | [] -> []
      | (eqns, ps, rhs) :: clause -> (
          let clause = aux_clause clause in
          let opt =
            List.fold_left
              (fun acc eqn ->
                 match (acc, eqn) with
                 | Some acc, EqualPat (relv, env, l, r, a) -> (
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
    | Constr (c0, _, _, ns), PConstr (c, ps), Ind (d0, ss, ms, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        if Constr.equal c0 c then
          let c1 = State.find_constr c0 ss in
          let param, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          ps_simpl relv ctx env ns ps tele
        else
          None
      else
        failwith "trans12.Logical.p_simpl"
    | Constr _, _, Ind _ -> Some [ EqualPat (relv, env, m, p, a) ]
    | _, PConstr (c, _), Ind (d0, ss, _, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        Some [ EqualPat (relv, env, m, p, a) ]
      else
        failwith "trans12.Logical.p_simpl"
    | m, p, a -> Some [ EqualPat (relv, env, m, p, a) ]

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
    Debug.exec (fun () -> pr "@[Program.infer_tm(%a)@]@." pp_tm m);
    match m with
    (* inference *)
    | Ann (m, a) ->
      let _ = Logical.infer_sort ctx env a in
      let m_elab, usg = check_tm ctx env m a in
      (a, m_elab, usg)
    | IMeta _ -> failwith "trans12.Program.infer_tm(IMeta)"
    | PMeta _ -> failwith "trans12.Program.infer_tm(PMeta)"
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
    | Fun (_, a, bnd) ->
      let x, cls = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      let relvs, ctree, usg = check_cls (Ctx.add_var x a s ctx) env cls a in
      let usg =
        match s with
        | U -> Usage.remove_var x usg R U
        | L -> Usage.remove_var x usg N L
        | _ -> failwith "trans12.Program.infer_tm(Fun)"
      in Syntax2.(a, _Fun relvs (bind_var (trans_var x) ctree), usg)
    | App (m, n) -> 
      let t, m_elab, usg1 = infer_tm ctx env m in
      (match whnf env t with
       | Pi (N, s, a, bnd) ->
         Logical.check_tm ctx env n a;
         Syntax2.(subst bnd n, _App (trans_sort s) m_elab _NULL, usg1)
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
      Syntax2.(b, n_elab, usg)
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
    | Constr (c0, ss, ms, ns) -> 
      List.iter Logical.assert_sort ss;
      let c1 = State.find_constr c0 ss in
      let ptl, relv = Ctx.find_constr c1 ctx in
      (match relv with
       | R ->
         let a, ns_elab, usg = infer_ptl ctx env ms ns ptl in
         Syntax2.(a, _Constr c1 (box_list ns_elab), usg)
       | _ -> failwith "trans12.Program.infer_tm(Constr)")
    | Match (_, ms, a, cls) ->
      let b, ms_elab, usg1 = infer_motive ctx env ms a in
      Debug.exec (fun () -> pr "Program.infer_motive_ok@.");
      let _, ctree, usg2 = check_cls ctx env cls a in
      let ms_elab = box_array (Array.of_list ms_elab) in
      let usg = Usage.merge usg1 usg2 in
      Syntax2.(b, lift_tm (msubst (unbox ctree) (unbox ms_elab)), usg)
    (* monad *)
    | IO _ -> failwith "trans12.Program.infer_tm(IO)"
    | Return m ->
      let a, m_elab, usg = infer_tm ctx env m in
      Syntax2.(IO a, _Return m_elab, usg)
    | MLet (m, bnd) ->
      let t1, m_elab, usg1 = infer_tm ctx env m in
      (match whnf env t1 with
       | IO a -> 
         let s = Logical.infer_sort ctx env a in
         let x, n = unbind bnd in
         let t2, n_elab, usg2 = infer_tm (Ctx.add_var x a s ctx) env n in
         let usg = Usage.(merge usg1 (remove_var x usg2 R s)) in
         (match whnf env t2 with
          | IO b -> Syntax2.(IO b, _MLet m_elab (bind_var (trans_var x) n_elab), usg)
          | _ -> failwith "trans12.Program.infer_tm(MLet)")
       | _ -> failwith "trans12.Program.infer_tm(MLet)")
    (* primitive types *)
    | Int_t -> failwith "trans12.Program.infer_tm(Int_t)"
    | Char_t -> failwith "trans12.Program.infer_tm(Char_t)"
    | String_t -> failwith "trans12.Program.infer_tm(String_t)"
    (* primitive terms *)
    | Int i -> Syntax2.(Int_t, _Int i, Usage.empty)
    | Char c -> Syntax2.(Char_t, _Char c, Usage.empty)
    | String s -> Syntax2.(String_t, _String s, Usage.empty)
    (* primitive operators *)
    | Neg m ->
      let m_elab, usg = check_tm ctx env m Int_t in
      Syntax2.(Int_t, _Neg m_elab, usg)
    | Add (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Int_t, _Add m_elab n_elab, Usage.merge usg1 usg2)
    | Sub (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Int_t, _Sub m_elab n_elab, Usage.merge usg1 usg2)
    | Mul (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Int_t, _Mul m_elab n_elab, Usage.merge usg1 usg2)
    | Div (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Int_t, _Div m_elab n_elab, Usage.merge usg1 usg2)
    | Mod (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Int_t, _Mod m_elab n_elab, Usage.merge usg1 usg2)
    | Lte (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Ind (bool_ind, [], [], []), _Lte m_elab n_elab, Usage.merge usg1 usg2)
    | Gte (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Ind (bool_ind, [], [], []), _Gte m_elab n_elab, Usage.merge usg1 usg2)
    | Lt (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Ind (bool_ind, [], [], []), _Lt m_elab n_elab, Usage.merge usg1 usg2)
    | Gt (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Ind (bool_ind, [], [], []), _Gt m_elab n_elab, Usage.merge usg1 usg2)
    | Eq (m, n) ->
      let m_elab, usg1 = check_tm ctx env m Int_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Ind (bool_ind, [], [], []), _Eq m_elab n_elab, Usage.merge usg1 usg2)
    | Chr m ->
      let m_elab, usg = check_tm ctx env m Int_t in
      Syntax2.(Char_t, _Chr m_elab, usg)
    | Ord m ->
      let m_elab, usg = check_tm ctx env m Char_t in
      Syntax2.(Int_t, _Ord m_elab, usg)
    | Push (m, n) ->
      let m_elab, usg1 = check_tm ctx env m String_t in
      let n_elab, usg2 = check_tm ctx env n Char_t in
      Syntax2.(String_t, _Push m_elab n_elab, Usage.merge usg1 usg2)
    | Cat (m, n) ->
      let m_elab, usg1 = check_tm ctx env m String_t in
      let n_elab, usg2 = check_tm ctx env n String_t in
      Syntax2.(String_t, _Cat m_elab n_elab, Usage.merge usg1 usg2)
    | Size m ->
      let m_elab, usg = check_tm ctx env m String_t in
      Syntax2.(Int_t, _Size m_elab, usg)
    | Indx (m, n) ->
      let m_elab, usg1 = check_tm ctx env m String_t in
      let n_elab, usg2 = check_tm ctx env n Int_t in
      Syntax2.(Char_t, _Indx m_elab n_elab, Usage.merge usg1 usg2)
    (* primitive sessions *)
    | Proto -> failwith "trans12.Program.infer_tm(Proto)"
    | Act _ -> failwith "trans12.Program.infer_tm(Act)"
    | End -> failwith "trans12.Program.infer_tm(End)"
    | Ch _ -> failwith "trans12.Program.infer_tm(Ch)"
    (* primitive effects *)
    | Print m -> 
      let m_elab, usg = check_tm ctx env m String_t in
      Syntax2.(IO (Ind (unit_ind, [], [], [])), _Print m_elab, usg)
    | Prerr m -> 
      let m_elab, usg = check_tm ctx env m String_t in
      Syntax2.(IO (Ind (unit_ind, [], [], [])), _Prerr m_elab, usg)
    | ReadLn m -> 
      let m_elab, usg = check_tm ctx env m (Ind (unit_ind, [], [], [])) in
      Syntax2.(IO String_t, _ReadLn m_elab, usg)
    | Fork m -> 
      let t, m_elab, usg = infer_tm ctx env m in
      (match whnf env t with
       | Pi (R, L, a, bnd) ->
         (match whnf env a with
          | Ch (role, a) ->
            let _, b = unbind bnd in
            Logical.assert_equal env b (IO (Ind (unit_ind, [], [], [])));
            Syntax2.(IO (Ch (not role, a)), _Fork m_elab, usg)
          | _ -> failwith "trans12.Program.infer_tm(Fork)")
       | _ -> failwith "trans12.Program.infer_tm(Fork)")
    | Send m ->
      let t, m_elab, usg = infer_tm ctx env m in
      (match whnf env t with
       | Ch (role1, Act (relv, role2, a, bnd)) when role1 = role2 ->
         let x, b = unbind bnd in
         let s = Logical.infer_sort ctx env a in
         let bnd = unbox (bind_var x (lift_tm (IO (Ch (role1, b))))) in
         Syntax2.(Pi (relv, L, a, bnd), _Send (trans_relv relv) (trans_sort s) m_elab, usg)
       | _ -> failwith "trans12.Program.infer_tm(Send)")
    | Recv m ->
      let t, m_elab, usg = infer_tm ctx env m in
      (match whnf env t with
       | Ch (role1, Act (relv, role2, a, bnd)) when role1 <> role2 ->
         let x, b = unbind bnd in
         let s = Logical.infer_sort ctx env a in
         let _b_t = _Pi R _U (lift_tm a) (bind_var x (_Type _L)) in
         let _b = _Lam _b_t x (_Ch role1 (lift_tm b)) in
         let ind = match relv with N -> exists0_ind | R -> exists1_ind in
         let t = Ind (ind, [s; L], [a; unbox _b], []) in
         Syntax2.(IO t, _Recv (trans_relv relv) (trans_sort s) m_elab, usg)
       | _ -> failwith "trans12.Program.infer_tm(Recv)")
    | Close m ->
      let t, m_elab, usg = infer_tm ctx env m in
      (match whnf env t with
       | Ch (role, End) ->
         Syntax2.(IO (Ind (unit_ind, [], [], [])), _Close role m_elab, usg)
       | _ -> failwith "trans12.Program.infer_tm(Close)")
    (* magic *)
    | Magic a ->
      let _ = Logical.infer_sort ctx env a in
      Syntax2.(a, _Magic, Usage.of_ctx ctx)

  and infer_ptl ctx env ms ns ptl =
    let rec aux_param ms ptl =
      match (ms, ptl) with
      | [], PBase tl -> aux_tele ns tl
      | m :: ms, PBind (a, bnd) ->
        Logical.check_tm ctx env m a;
        aux_param ms (subst bnd m)
      | _ -> failwith "trans12.Program.infer_ptl(param)"
    and aux_tele ns tl =
      match (ns, tl) with
      | [], TBase a -> (a, [], Usage.empty)
      | n :: ns, TBind (N, a, bnd) ->
        Logical.check_tm ctx env n a;
        let b, ns_elab, usg = aux_tele ns (subst bnd n) in
        Syntax2.(b, _NULL :: ns_elab, usg)
      | n :: ns, TBind (R, a, bnd) ->
        let n_elab, usg1 = check_tm ctx env n a in
        let b, ns_elab, usg2 = aux_tele ns (subst bnd n) in
        Syntax2.(b, n_elab :: ns_elab, Usage.merge usg1 usg2)
      | _ -> failwith "trans12.Program.infer_ptl(tele)"
    in
    aux_param ms ptl

  and infer_motive ctx env ms a =
    match (ms, whnf env a) with
    | [], a -> (a, [], Usage.empty)
    | m :: ms, Pi (N, L, a, bnd) ->
      Debug.exec (fun () ->
          pr "Program.infer_motive_N(%a, %a)@." pp_tm m pp_tm a);
      Logical.check_tm ctx env m a;
      Debug.exec (fun () ->
          pr "Program.infer_motive_N_ok(%a, %a)@." pp_tm m pp_tm a);
      let b, ms_elab, usg = infer_motive ctx env ms (subst bnd m) in
      Syntax2.(b, _NULL :: ms_elab, usg)
    | m :: ms, Pi (R, L, a, bnd) ->
      Debug.exec (fun () ->
          pr "Program.infer_motive_R(%a, %a)@." pp_tm m pp_tm a);
      let m_elab, usg1 = check_tm ctx env m a in
      Debug.exec (fun () ->
          pr "Program.infer_motive_R_ok(%a, %a)@." pp_tm m pp_tm a);
      let b, ms_elab, usg2 = infer_motive ctx env ms (subst bnd m) in
      Syntax2.(b, m_elab :: ms_elab, Usage.merge usg1 usg2)
    | _ -> failwith "trans12.Program.infer_motive"

  and check_tm ctx env m a =
    Debug.exec (fun () ->
        pr "@[Program.check_tm(@;<1 2>@[%a@],@;<1 2>@[%a@]@;<1 0>)@]@." pp_tm m
          pp_tm a);
    let b, m_elab, usg = infer_tm ctx env m in
    Logical.assert_equal env a b;
    (m_elab, usg)

  and check_cls ctx env cls a =
    let infer_demote ctx env a =
      let ctx = Ctx.map_var demote_pmeta ctx in
      Logical.infer_sort ctx env (demote_pmeta a)
    in
    let rec is_absurd eqns rhs =
      match (eqns, rhs) with
      | EqualPat (_, _, PMeta _, PAbsurd, _) :: _, None -> true
      | EqualPat (_, _, PMeta _, PAbsurd, _) :: _, Some _ ->
        failwith "trans12.Program.is_absurd"
      | _ :: eqns, _ -> is_absurd eqns rhs
      | [], _ -> false
    in
    let rec get_absurd = function
      | EqualPat (_, _, PMeta _, PAbsurd, a) :: _ -> a
      | _ :: eqns -> get_absurd eqns
      | [] -> failwith "trans12.Program.get_absurd"
    in
    let rec can_split = function
      | EqualPat (_, _, PMeta _, PConstr _, _) :: _ -> true
      | _ :: eqns -> can_split eqns
      | [] -> false
    in
    let rec first_split = function
      | EqualPat (relv, _, PMeta x, PConstr _, a) :: _ -> (relv, x, a)
      | _ :: eqns -> first_split eqns
      | [] -> failwith "trans12.Program.first_split"
    in
    let fail_on_ind global ctx d1 ss ms a =
      let _, cs0 = Ctx.find_ind d1 ctx in
      List.iter (fun c0 ->
          let c1 = State.find_constr c0 ss in
          let param, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          let _, t = unbind_tele tele in
          let global = EqualTerm (env, a, t) :: global in
          if not (witness_distinct global) then
            failwith "trans12.Program.fail_on_ind(%a)" Ind.pp d1)
        cs0
    in
    let rec aux_prbm ctx env prbm a =
      match prbm.clause with
      (* empty *)
      | [] ->
        Debug.exec (fun () -> pr "case_empty@.");
        if not (witness_distinct prbm.global) then
          match whnf env a with
          | Pi (_, _, a, _) ->
            (match whnf env a with
             | Ind (d0, ss, ms, ns) ->
               let d1 = State.find_ind d0 ss in
               fail_on_ind prbm.global ctx d1 ss ms a;
               Syntax2.([], _Absurd, Usage.of_ctx ctx)
             | _ -> failwith "trans12.Program.check_cls(Empty)")
          | _ -> failwith "trans12.Program.check_cls(Empty)"
        else Syntax2.([], _Absurd, Usage.of_ctx ctx)
      (* case intro *)
      | (eqns, p :: ps, rhs) :: clause ->
        (match whnf env a with
         | Pi (relv, s, a, bnd) ->
           let x, b = unbind_pmeta bnd in
           Debug.exec (fun () ->
               pr "trans12.Program.case_intro(%a, %a)@." Var.pp x pp_tm a);
           let t = infer_demote ctx env a in
           let ctx = Ctx.add_var x a t ctx in
           let prbm = prbm_add env prbm x a relv in
           let rxs, ctree, usg = aux_prbm ctx env prbm b in
           let usg = Usage.remove_var x usg relv t in
           Debug.exec (fun () -> pr "trans12.Program.case_introed(%a)@." pp_tm a);
           (match s with
            | U ->
              Syntax2.
                ( ((trans_relv relv, U), trans_var x) :: rxs
                , ctree
                , Usage.refine_pure usg )
            | L -> Syntax2.(((trans_relv relv, L), trans_var x) :: rxs, ctree, usg)
            | _ -> failwith "trans12.Program.check_cls(Intro(%a))" pp_tm a)
         | a -> failwith "trans12.Program.check_cls(Intro(%a))" pp_tm a)
      (* case split *)
      | (eqns, [], rhs) :: _ when can_split eqns -> 
        let relv, x, b = first_split eqns in
        let s = infer_demote ctx env b in
        let x_elab, usg1 =
          match relv with
          | R -> Syntax2.(_Var (trans_var x), Usage.var_singleton x (s, false))
          | N -> Syntax2.(_NULL, Usage.empty)
        in
        (match whnf env b with
         | Ind (d0, ss, ms, _) ->
           let d1 = State.find_ind d0 ss in
           let _, cs0 = Ctx.find_ind d1 ctx in
           let ctrees, usg2 = List.fold_left (fun (ctrees, usg2) c0 ->
               let c1 = State.find_constr c0 ss in
               Debug.exec (fun () ->
                   pr "trans12.Program.case_split(%a, %a)@." Ind.pp d1
                     Constr.pp c1);
               let param, _ = Ctx.find_constr c1 ctx in
               let tele = param_inst param ms in
               let args, t = unbind_tele tele in
               let ctx, args = List.fold_left_map (fun ctx (relv, x, a) ->
                   let s = infer_demote ctx env a in
                   (Ctx.add_var x a s ctx, ((relv, x, s), PMeta x)))
                   ctx args
               in
               let args, ns = List.split args in
               let m = Constr (c0, ss, ms, ns) in
               let var_map = Var.Map.singleton x m in
               let a = subst_pmeta var_map a in
               let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
               let prbm = prbm_simpl ctx var_map prbm in
               let prbm = { prbm with global = EqualTerm (env, b, t) :: prbm.global } in
               let _, ctree, usg = aux_prbm ctx env prbm a in
               let usg = List.fold_left (fun usg (relv0, x, s) ->
                   match relv with
                   | N -> Usage.remove_var x usg N s
                   | R -> Usage.remove_var x usg relv0 s)
                   usg args
               in
               let xs = List.map (fun (_, x, _) -> trans_var x) args in
               let ctree = Syntax2.(_PConstr c1 (bind_mvar (Array.of_list xs) ctree)) in
               (ctree :: ctrees, Usage.refine_equal usg2 usg))
               ([], Usage.of_ctx ctx) cs0
           in
           let ctrees = box_rev_list ctrees in
           Syntax2.
             ( []
             , _Match (trans_relv relv) (trans_sort s) x_elab ctrees
             , Usage.merge usg1 usg2 )
         | _ -> failwith "trans12.Program.check_cls(Split(%a))" pp_tm b)
      (* absurd pattern *)
      | (eqns, [], rhs) :: _ when is_absurd eqns rhs ->
        Debug.exec (fun () -> pr "trans12.Program.case_absurd@.");
        if not (witness_distinct prbm.global) then
          let a = get_absurd eqns in
          match whnf env a with
          | Ind (d0, ss, ms, ns) ->
            let d1 = State.find_ind d0 ss in
            fail_on_ind prbm.global ctx d1 ss ms a;
            Syntax2.([], _Absurd, Usage.of_ctx ctx)
          | _ -> failwith "trans12.Program.check_cls(Absurd)"
        else Syntax2.([], _Absurd, Usage.of_ctx ctx)
      (* case coverage *)
      | (eqns, [], rhs) :: _ -> (
          Debug.exec (fun () ->
              pr "@[<v 0>case_coverage{|@;<1 2>%a@;<1 0>|}@]@." pp_pprbm prbm);
          match rhs with
          | Some rhs ->
            let local_map, global_map = unify_pprbm eqns prbm.global in
            let a = resolve_pmeta global_map a in
            let ctx = Ctx.map_var (resolve_pmeta global_map) ctx in
            let env = Env.merge_var (Var.Map.map demote_pmeta global_map) env in
            let rhs = resolve_pmeta local_map rhs in
            Debug.exec (fun () ->
                pr "@[case_coverage_ok(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm rhs pp_tm a);
            let rhs_elab, usg = check_tm ctx env rhs a in
            ([], rhs_elab, usg)
          | None ->
            if not (witness_distinct prbm.global)
            then failwith "trans12.Program.check_cls(Cover)"
            else Syntax2.([], _Absurd, Usage.of_ctx ctx))
    in
    let rxs, ctree, usg = aux_prbm ctx env (of_cls cls) a in
    let relvs, xs = List.split rxs in
    (relvs, bind_mvar (Array.of_list xs) ctree, usg)

  and prbm_add env prbm x a relv =
    match prbm.clause with
    | [] -> prbm
    | (eqns, p :: ps, rhs) :: clause ->
      let prbm = prbm_add env { prbm with clause } x a relv in
      let clause = (eqns @ [ EqualPat (relv, env, PMeta x, p, a) ], ps, rhs) :: prbm.clause in
      { prbm with clause }
    | _ -> failwith "trans12.Program.prbm_add"

  and prbm_simpl ctx var_map prbm =
    let rec aux_global = function
      | [] -> []
      | EqualTerm (env, a, b) :: eqns ->
        let a = subst_pmeta var_map a in
        let b = subst_pmeta var_map b in
        let eqns = aux_global eqns in
        EqualTerm (env, a, b) :: eqns
      | EqualPat _ :: _ -> failwith "trans12.Program.prbm_simpl(Global)"
    in
    let rec aux_clause = function
      | [] -> []
      | (eqns, ps, rhs) :: clause -> 
        let clause = aux_clause clause in
        let opt = List.fold_left (fun acc eqn ->
            match (acc, eqn) with
            | Some acc, EqualPat (relv, env, l, r, a) ->
              let l = subst_pmeta var_map l in
              let a = subst_pmeta var_map a in
              (match p_simpl relv ctx env l r a with
               | Some eqns -> Some (acc @ eqns)
               | None -> None)
            | _ -> None)
            (Some []) eqns
        in
        (match opt with
         | Some eqns -> (eqns, ps, rhs) :: clause
         | None -> clause)
    in
    let global = aux_global prbm.global in
    let clause = aux_clause prbm.clause in
    { global; clause }

  and p_simpl relv ctx env m p a =
    let a = whnf env a in
    match (m, p, a) with
    | Constr (c0, _, _, ns), PConstr (c, ps), Ind (d0, ss, ms, _) ->
      Debug.exec (fun () -> pr "%a@." Constr.pp c0);
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        if Constr.equal c0 c then
          let c1 = State.find_constr c0 ss in
          let param, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          ps_simpl relv ctx env ns ps tele
        else None
      else failwith "trans12.Program.p_simpl1(%a, %a, %a)" pp_tm m pp_p p pp_tm a
    | Constr _, _, Ind _ -> Some [ EqualPat (relv, env, m, p, a) ]
    | _, PConstr (c, _), Ind (d0, ss, _, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0
      then Some [ EqualPat (relv, env, m, p, a) ]
      else failwith "trans12.Program.p_simpl2(%a, %a, %a)" pp_tm m pp_p p pp_tm a
    | m, p, a -> Some [ EqualPat (relv, env, m, p, a) ]

  and ps_simpl relv0 ctx env ms ps tele =
    match (relv0, ms, ps, tele) with
    | R, m :: ms, p :: ps, TBind (relv, a, bnd) -> 
      let opt1 = p_simpl relv ctx env m p a in
      let tele = subst bnd m in
      let opt2 = ps_simpl relv0 ctx env ms ps tele in
      (match (opt1, opt2) with
       | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
       | _ -> None)
    (* sub-patterns inherit irrelevancy *)
    | N, m :: ms, p :: ps, TBind (_, a, bnd) ->
      let opt1 = p_simpl N ctx env m p a in
      let tele = subst bnd m in
      let opt2 = ps_simpl N ctx env ms ps tele in
      (match (opt1, opt2) with
       | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
       | _ -> None)
    | _, [], [], TBase _ -> Some []
    | _ -> None
end

let warn_const x e =
  match e with
  | Failure s ->
    epr "@[<v 0>warning - pruned constant %a@;<1 2>@[%s@]@]@." Const.pp x s
  | _ -> raise e

let warn_ind x e =
  match e with
  | Failure s ->
    epr "@[<v 0>warning - pruned inductive %a@;<1 2>@[%s@]@]@." Ind.pp x s
  | _ -> raise e

let warn_constr x e =
  match e with
  | Failure s ->
    epr "@[<v 0>warning - pruned constructor %a@;<1 2>@[%s@]@]@." Constr.pp x s
  | _ -> raise e

let warn_extern x e =
  match e with
  | Failure s ->
    epr "@[<v 0>warning - pruned extern %a@;<1 2>@[%s@]@]@." Const.pp x s
  | _ -> raise e

let const_extend x ss =
  match ss with
  | [] -> x
  | _ ->
    let ss = String.concat "" (List.map (str "%a" pp_sort) ss) in
    Const.extend x ss

let ind_extend d ss =
  match ss with
  | [] -> d
  | _ ->
    let ss = String.concat "" (List.map (str "%a" pp_sort) ss) in
    Ind.extend d ss

let constr_extend c ss =
  match ss with
  | [] -> c
  | _ ->
    let ss = String.concat "" (List.map (str "%a" pp_sort) ss) in
    Constr.extend c ss

let make_init xs =
  let rec loop xs =
    match xs with
    | [] -> [ [] ]
    | _ :: xs ->
      let ss = loop xs in
      let ssU = List.(map (cons U)) ss in
      let ssL = List.(map (cons L)) ss in
      ssU @ ssL
  in
  loop (Array.to_list xs)

let rec check_dcls ctx env = function
  | [] -> ([], Usage.empty)
  | Definition { name = x0; relv = R; scheme = sch } :: _ when Const.is_main x0 -> 
    let sargs, (m, a) = unmbind sch in
    (match (sargs, whnf env a) with
     | [||], IO a -> 
       Logical.assert_equal env a (Ind (unit_ind, [], [], []));
       let m_elab, usg = Program.check_tm ctx env m (IO a) in
       Syntax2.([ Main { body = unbox m_elab } ], usg)
     | _ -> failwith "trans12.check_dcls(Main)")
  | Definition { name = x0; relv = N; scheme = sch } :: dcls ->
    let sargs = mbinder_names sch in
    let init = make_init sargs in
    let dcl_elab, res, ctx, local, xs =
      List.fold_right (fun ss (dcl_elab, res, ctx_acc, local, xs) ->
          let x1 = const_extend x0 ss in
          try
            let m, a = msubst sch (Array.of_list ss) in
            let s = Logical.infer_sort ctx env a in
            Logical.check_tm ctx env m a;
            ( Syntax2.(Definition { name = x1; relv = N; body = NULL })
              :: dcl_elab
            , RMap.add ss x1 res
            , Ctx.add_const x1 a s ctx_acc
            , RMap.add ss m local
            , (x1, s) :: xs )
          with e -> warn_const x1 e; (dcl_elab, res, ctx_acc, local, xs))
        init ([], RMap.empty, ctx, RMap.empty, [])
    in
    State.add_const x0 res;
    let env = Env.add_const x0 (fun ss -> RMap.find_opt ss local) env in
    let dcls_elab, usg = check_dcls ctx env dcls in
    let usg = List.fold_left (fun usg (x, s) -> Usage.remove_const x usg N s) usg xs in
    (dcl_elab @ dcls_elab, usg)
  | Definition { name = x0; relv = R; scheme = sch } :: dcls ->
    let sargs = mbinder_names sch in
    let init = make_init sargs in
    let dcl_elab, res, ctx, local, xs, usg1 =
      List.fold_right (fun ss (dcl_elab, res, ctx_acc, local, xs, usg1) ->
          let x1 = const_extend x0 ss in
          try
            let m, a = msubst sch (Array.of_list ss) in
            let s = Logical.infer_sort ctx env a in
            let m_elab, usg = Program.check_tm ctx env m a in
            ( Syntax2.(Definition { name = x1; relv = R; body = unbox m_elab })
              :: dcl_elab
            , RMap.add ss x1 res
            , Ctx.add_const x1 a s ctx_acc
            , RMap.add ss m local
            , (x1, s) :: xs
            , Usage.merge usg usg1 )
          with e -> warn_const x1 e; (dcl_elab, res, ctx_acc, local, xs, usg1))
        init ([], RMap.empty, ctx, RMap.empty, [], Usage.empty)
    in
    State.add_const x0 res;
    let env = Env.add_const x0 (fun ss -> RMap.find_opt ss local) env in
    let dcls_elab, usg2 = check_dcls ctx env dcls in
    let usg2 = List.fold_left (fun usg2 (x, s) -> Usage.remove_const x usg2 R s) usg2 xs in
    (dcl_elab @ dcls_elab, Usage.merge usg1 usg2)
  | Inductive { name = d0; relv; arity; dconstrs = dcs } :: dcls ->
    let sargs = mbinder_names arity in
    let init = make_init sargs in
    let dcl_elab, ctx = List.fold_right (fun ss (dcl_elab, ctx_acc) ->
        let d1 = ind_extend d0 ss in
        try
          let arity = msubst arity (Array.of_list ss) in
          check_arity ctx env arity;
          State.add_ind d0 ss d1;
          let ctx = Ctx.add_ind d1 (arity, []) ctx in
          let dcs_elab, ctx_acc, cs0 = check_dconstrs ss ctx env relv d0 dcs ctx_acc in
          let ctx_acc = Ctx.add_ind d1 (arity, cs0) ctx_acc in
          Syntax2.
            ( Inductive
                { name = d1
                ; relv = Program.trans_relv relv
                ; body = dcs_elab
                }
              :: dcl_elab
            , ctx_acc )
        with e -> warn_ind d1 e; (dcl_elab, ctx_acc))
        init ([], ctx)
    in
    let dcls_elab, usg = check_dcls ctx env dcls in
    (dcl_elab @ dcls_elab, usg)
  | Extern { name = x0; relv; scheme = sch } :: dcls ->
    let sargs = mbinder_names sch in
    let init = make_init sargs in
    let dcl_elab, res, ctx, local, xs =
      List.fold_right (fun ss (dcl_elab, res, ctx_acc, local, xs) ->
          let x1 = const_extend x0 ss in
          try
            let m_opt, a = msubst sch (Array.of_list ss) in
            let s = Logical.infer_sort ctx env a in
            let relv = Program.trans_relv relv in
            match m_opt with
            | Some m ->
              Logical.check_tm ctx env m a;
              ( Syntax2.(Extern { name = x1; relv }) :: dcl_elab
              , RMap.add ss x1 res
              , Ctx.add_const x1 a s ctx_acc
              , RMap.add ss m local
              , (x1, s) :: xs )
            | None ->
              ( Syntax2.(Extern { name = x1; relv }) :: dcl_elab
              , RMap.add ss x1 res
              , Ctx.add_const x1 a s ctx_acc
              , local
              , (x1, s) :: xs )
          with e -> warn_extern x1 e; (dcl_elab, res, ctx_acc, local, xs))
        init ([], RMap.empty, ctx, RMap.empty, [])
    in
    State.add_const x0 res;
    let env = Env.add_const x0 (fun ss -> RMap.find_opt ss local) env in
    let dcls_elab, usg = check_dcls ctx env dcls in
    let usg = List.fold_left (fun usg (x, s) -> Usage.remove_const x usg relv s) usg xs in
    (dcl_elab @ dcls_elab, usg)

and check_arity ctx env arity =
  let rec aux_param ctx = function
    | PBase tele -> aux_tele ctx tele
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      aux_param (Ctx.add_var x a s ctx) b
  and aux_tele ctx = function
    | TBase (Type U) -> ()
    | TBase (Type L) -> ()
    | TBind (R, a, bnd) ->
      let x, b = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      aux_tele (Ctx.add_var x a s ctx) b
    | _ -> failwith "trans12.check_arity"
  in
  aux_param ctx arity

and check_dconstrs ss ctx env relv d0 dconstrs ctx_acc =
  let rec aux_param ctx env relv d0 = function
    | PBase tele -> fst (aux_tele ctx env relv d0 tele)
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      aux_param (Ctx.add_var x a s ctx) env relv d0 b
  and aux_tele ctx env relv d0 = function
    | TBase (Ind (d, _, _, _) as a) when Ind.equal d d0 ->
      let t = Logical.infer_sort ctx env a in
      ([], t)
    | TBind (N, a, bnd) ->
      let x, b = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      let layout, t = aux_tele (Ctx.add_var x a s ctx) env relv d0 b in
      Syntax2.(N :: layout, t)
    | TBind (R, a, bnd) ->
      let x, b = unbind bnd in
      let s = Logical.infer_sort ctx env a in
      let layout, t = aux_tele (Ctx.add_var x a s ctx) env relv d0 b in
      if relv = N || s <= t then
        Syntax2.(R :: layout, t)
      else
        failwith "trans12.check_dconstrs"
    | _ -> failwith "trans12.check_dconstrs"
  in
  match dconstrs with
  | [] -> ([], ctx_acc, [])
  | (c0, sch) :: dconstrs -> (
      let c1 = constr_extend c0 ss in
      let opt =
        try
          let param = msubst sch (Array.of_list ss) in
          let i = aux_param ctx env relv d0 param in
          Some (i, param)
        with
        | e ->
          warn_constr c1 e;
          None
      in
      let dconstrs_elab, ctx_acc, cs0 =
        check_dconstrs ss ctx env relv d0 dconstrs ctx_acc
      in
      match opt with
      | Some (layout, param) ->
        State.add_constr c0 ss c1;
        let ctx_acc = Ctx.add_constr c1 (param, relv) ctx_acc in
        ((c1, layout) :: dconstrs_elab, ctx_acc, c0 :: cs0)
      | None -> (dconstrs_elab, ctx_acc, cs0))

let trans_dcls dcls =
  let dcls, usg = check_dcls Ctx.empty Env.empty dcls in
  Usage.assert_empty usg;
  dcls
