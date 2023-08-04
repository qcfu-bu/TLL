open Bindlib
open Names

(* sorts *)
type sort =
  | U
  | L
  | SVar of sort var
  | SMeta of SMeta.t * sorts

and sorts = sort list

(* relevancy *)
type relv =
  | N
  | R

(* terms *)
type tm =
  (* inference *)
  | Ann of tm * tm
  | IMeta of IMeta.t * sorts * tms
  (* core *)
  | Type of sort
  | Var of tm var
  | Const of Const.t * sorts
  | Pi of relv * sort * tm * (tm, tm) binder
  | Fun of tm * (tm, cls) binder
  | App of tm * tm
  | Let of relv * tm * (tm, tm) binder
  (* inductive *)
  | Ind of Ind.t * sorts * tms * tms
  | Constr of Constr.t * sorts * tms * tms
  | Match of tms * tm * cls
  (* monad *)
  | IO of tm
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* magic *)
  | Magic of tm

and tms = tm list

(* unbound pattern *)
and p =
  | PVar of tm var
  | PAbsurd
  | PMul of Constr.t * ps
  | PAdd of Constr.t * int * ps

and ps = p list

(* bound pattern *)
and p0 =
  | P0Rel
  | P0Absurd
  | P0Mul of Constr.t * p0s
  | P0Add of Constr.t * int * p0s

and p0s = p0 list

(* clause *)
and cl = p0s * (tm, tm option) mbinder
and cls = cl list

(* declarations *)
type dcl =
  | Definition of
      { name : Const.t
      ; relv : relv
      ; body : (tm * tm) scheme
      }
  | Inductive of
      { name : Ind.t
      ; relv : relv
      ; body : (tele * dconstrs) param scheme
      }

and dcls = dcl list

and dconstr =
  | DMul of Constr.t * tele
  | DAdd of Constr.t * tele

and dconstrs = dconstr list
and 'a scheme = (sort, 'a) mbinder

and 'a param =
  | PBase of 'a
  | PBind of tm * (tm, 'a param) binder

and tele =
  | TBase of tm
  | TBind of relv * tm * (tm, tele) binder
