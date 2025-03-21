open Bindlib
open Names

(* sorts *)
type sort =
  | U
  | L

(* relevancy *)
type relv =
  | N
  | R

type relvs = (relv * sort) list

(* terms *)
type tm =
  (* core *)
  | Var of tm var
  | Const of Const.t
  | Fun of relvs * (tm, (tm, tm) mbinder) binder
  | App of sort * tm * tm
  | Let of tm * (tm, tm) binder
  (* inductive *)
  | Constr of Constr.t * tms
  | Match of relv * sort * tm * cls
  | Absurd
  (* monad *)
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* erasure *)
  | NULL
  (* magic *)
  | Magic

and tms = tm list
and cl = Constr.t * (tm, tm) mbinder
and cls = cl list

type dcl =
  | Main of { body : tm }
  | Definition of
      { name : Const.t
      ; relv : relv
      ; body : tm
      }
  | Inductive of
      { name : Ind.t
      ; relv : relv
      ; body : dconstrs
      }
  | Extern of
      { name : Const.t
      ; relv : relv
      }

and dconstr = Constr.t * relv list
and dconstrs = dconstr list

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

(* relv *)
let _N = box N
let _R = box R

(* core *)
let _Var = box_var
let _Const x = box (Const x)
let _Fun relvs = box_apply (fun m -> Fun (relvs, m))
let _App s = box_apply2 (fun m n -> App (s, m, n))
let _Let = box_apply2 (fun m n -> Let (m, n))

(* inductive *)
let _Constr x = box_apply (fun ms -> Constr (x, ms))
let _Match r s = box_apply2 (fun m cls -> Match (r, s, m, cls))
let _Absurd = box Absurd

(* monad *)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m n -> MLet (m, n))

(* erasure *)
let _NULL = box NULL

(* magic *)
let _Magic = box Magic

(* clause *)
let _PConstr x = box_apply (fun rhs -> (x, rhs))

(* spine forms *)
let unApps m =
  let rec aux m ns =
    match m with
    | App (s, m, n) -> aux m ((n, s) :: ns)
    | _ -> (m, ns)
  in
  aux m []

(* box *)
let box_relv = function
  | N -> _N
  | R -> _R

let box_sort = function
  | U -> _U
  | L -> _L

let rec lift_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Fun (relvs, bnd) -> _Fun relvs (box_binder (box_mbinder lift_tm) bnd)
  | App (s, m, n) -> _App s (lift_tm m) (lift_tm n)
  | Let (m, bnd) -> _Let (lift_tm m) (box_binder lift_tm bnd)
  (* inductive *)
  | Constr (c, ms) ->
    let ms = List.map lift_tm ms in
    _Constr c (box_list ms)
  | Match (relv, s, m, cls) ->
    let cls =
      List.map (fun (c, bnd) -> _PConstr c (box_mbinder lift_tm bnd)) cls
    in
    _Match relv s (lift_tm m) (box_list cls)
  | Absurd -> _Absurd
  (* monad *)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* erasure *)
  | NULL -> _NULL
  (* magic *)
  | Magic -> _Magic
