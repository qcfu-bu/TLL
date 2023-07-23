open Bindlib
open Names

(* sorts *)
type sort =
  | U
  | L
  | SVar of sort var
  | SMeta of SMeta.t * sorts

and sorts = sort array

(* relevancy *)
type rel =
  | N
  | R

(* terms *)
type tm =
  (* inference *)
  | Ann of tm * tm
  | IMeta of IMeta.t * sorts * tms (* implict inference *)
  | PMeta of PMeta.t (* pattern inference *)
  (* core *)
  | Type of sort
  | Var of tm var
  | Const of Const.t * sorts
  | Pi of rel * sort * tm * (tm, tm) binder
  | Lam of rel * sort * tm * (tm, tm) binder
  | Fix of int * tm * (tm, tm) binder
  | App of tm * tm
  | Let of rel * tm * (tm, tm) binder
  (* inductive *)
  | Ind of Ind.t * sorts
  | Constr of Constr.t * sorts
  | Match of (tm * rel) array * tm * cls
  | Absurd
  (* record *)
  | Record of sort * tm Proj.Map.t
  | Struct of sort * tm Proj.Map.t
  | Proj of Proj.t * tm

and consts = Const.t array
and tms = tm array

(* unbound pattern *)
and p =
  | PVar of tm var
  | PConstr of Constr.t * ps

and ps = p array

(* bound pattern *)
and p0 =
  | P0Rel
  | P0Constr of Constr.t * p0s

and p0s = p0 array

(* clause *)
and cl = p0s * (tm, tm) mbinder
and cls = cl array

(* declarations *)
type dcl =
  | DTm of rel * Const.t * (tm * tm) scheme
  | DInd of rel * Ind.t * (tm * constrs) scheme

(* constructor *)
and constr = Constr.t * tm
and constrs = constr array

(* sort-polymorphic scheme *)
and 'a scheme = (sort, 'a) mbinder
