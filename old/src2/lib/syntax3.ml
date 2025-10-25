open Bindlib
open Names

(* sorts *)
type sort =
  | U
  | L

(* terms *)
type tm =
  (* core *)
  | Var of tm var
  | Const of Const.t
  | Fun of (tm, tm) binder
  | Lam0 of sort * tm
  | Lam1 of sort * (tm, tm) binder
  | App0 of sort * tm
  | App1 of sort * tm * tm
  | Let of tm * (tm, tm) binder
  (* inductive *)
  | Constr0 of Constr.t
  | Constr1 of Constr.t * tms
  | Match0 of tm * cl0s
  | Match1 of sort * tm * cl1s
  | Absurd
  (* magic *)
  | Magic

and tms = tm list
and cl0 = Constr.t * tm
and cl1 = Constr.t * (tm, tm) mbinder
and cl0s = cl0 list
and cl1s = cl1 list

type dcl =
  | Main of { body : tm }
  | Definition of
      { name : Const.t
      ; body : tm
      }

module Var = struct
  module Inner = struct
    open Fmt

    type t = tm var

    let mk = new_var (fun x -> Var x)
    let compare = compare_vars
    let pp fmt x = pf fmt "%s_%d" (name_of x) (uid_of x)
  end

  include Inner
  module Set = Set.Make (Inner)
  module Map = Map.Make (Inner)
end

(* smart constructors *)
let var x = Var x

(* sort *)
let _U = box U
let _L = box L

(* core *)
let _Var = box_var
let _Const x = box (Const x)
let _Fun = box_apply (fun bnd -> Fun bnd)
let _Lam0 s = box_apply (fun m -> Lam0 (s, m))
let _Lam1 s = box_apply (fun m -> Lam1 (s, m))
let _App0 s = box_apply (fun m -> App0 (s, m))
let _App1 s = box_apply2 (fun m n -> App1 (s, m, n))
let _Let = box_apply2 (fun m n -> Let (m, n))

(* inductive *)
let _Constr0 c = box (Constr0 c)
let _Constr1 c = box_apply (fun ms -> Constr1 (c, ms))
let _Match0 = box_apply2 (fun m cls -> Match0 (m, cls))
let _Match1 s = box_apply2 (fun m cls -> Match1 (s, m, cls))
let _Absurd = box Absurd

(* magic *)
let _Magic = box Magic

(* clause *)
let _PConstr x = box_apply (fun rhs -> (x, rhs))

(* spine forms *)
let unApps m =
  let rec aux m ns =
    match m with
    | App0 (s, m) -> aux m (None :: ns)
    | App1 (s, m, n) -> aux m (Some (n, s) :: ns)
    | _ -> (m, ns)
  in
  aux m []

(* box *)
let box_sort = function
  | U -> _U
  | L -> _L

let rec lift_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Fun bnd -> _Fun (box_binder lift_tm bnd)
  | Lam0 (s, bnd) -> _Lam0 s (lift_tm bnd)
  | Lam1 (s, bnd) -> _Lam1 s (box_binder lift_tm bnd)
  | App0 (s, m) -> _App0 s (lift_tm m)
  | App1 (s, m, n) -> _App1 s (lift_tm m) (lift_tm n)
  | Let (m, bnd) -> _Let (lift_tm m) (box_binder lift_tm bnd)
  (* inductive *)
  | Constr0 c -> _Constr0 c
  | Constr1 (c, ms) ->
    let ms = List.map lift_tm ms in
    _Constr1 c (box_list ms)
  | Match0 (m, cls) ->
    let cls = List.map (fun (c, m) -> _PConstr c (lift_tm m)) cls in
    _Match0 (lift_tm m) (box_list cls)
  | Match1 (s, m, cls) ->
    let cls =
      List.map (fun (c, bnd) -> _PConstr c (box_mbinder lift_tm bnd)) cls
    in
    _Match1 s (lift_tm m) (box_list cls)
  | Absurd -> _Absurd
  (* magic *)
  | Magic -> _Magic
