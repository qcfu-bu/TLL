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

module Logical = struct
  let assert_sort = function
    | U -> ()
    | L -> ()
    | _ -> failwith "trans12.Logical.assert_sort"

  let assert_equal env m n =
    if not (eq_tm env m n) then
      failwith "trans12.Logical.assert_equal(%a, %a)" pp_tm m pp_tm n

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
    | PMeta _ -> failwith "trans12.Logical.infer_tm(PMeta)"
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

  and infer_ptl ctx env ms ns ptl = _
  and infer_motive ctx env ms a = _
  and check_tm ctx env m a = _
  and check_cls ctx env cls a = _
end
