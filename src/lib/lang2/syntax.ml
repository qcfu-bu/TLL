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
type relv =
  | N
  | R

(* terms *)
type tm =
  (* inference *)
  | Ann of tm * tm
  | IMeta of IMeta.t * sorts * tms (* implict inference *)
  | TMeta of TMeta.t * sorts * tms (* trait inference *)
  (* core *)
  | Type of sort
  | Var of tm var
  | Const of Const.t * sorts
  | Pi of relv * sort * tm * (tm, tm) binder
  | Fun of tm * (tm, cls) binder
  | App of tm * tm
  | Let of relv * tm * (tm, tm) binder
  (* inductive *)
  | Ind of Ind.t * sorts
  | Constr of Constr.t * sorts
  | Match of tms * tm * cls
  | Absurd
  (* record *)
  | Record of Record.t * sorts
  | Struct of tm * (Field.t * relv * tm) array
  | Proj of Field.t * tm
  (* magic *)
  | Magic

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
  | DTm of
      { name : Const.t
      ; relv : relv
      ; body : (tm * tm) param scheme
      }
  | DInd of
      { name : Ind.t
      ; relv : relv
      ; body : (tm * constrs) param scheme
      }
  | DRec of
      { name : Record.t
      ; relv : relv
      ; body : (sort * fdef) param scheme
      }

and 'a param =
  | PBase of 'a
  | PBind of tm * (tm, 'a param) binder

and fdef =
  | Empty
  | Field of Field.t * relv * tm * (tm, fdef) binder

(* constructor *)
and constr = Constr.t * tm
and constrs = constr array

(* sort-polymorphic scheme *)
and 'a scheme = (sort, 'a) mbinder
