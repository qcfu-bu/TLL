type id = string
type ids = id list

type sort =
  | U
  | L
  | SId of id

type sorts = sort list

type relv =
  | N
  | R

type ('a, 'b) binder = Binder of 'a * 'b

type tm =
  (* inference *)
  | Ann of tm * tm
  (* core *)
  | Type of sort
  | Id of id
  | Inst of id * sorts
  | Pi of relv * sort * tm * (id, tm) binder
  | Lam of relv * sort * tm * (id, tm) binder
  | Fun of tm option * (id option, cls) binder
  | App of tms
  | Let of relv * tm * (id, tm) binder
  (* inductive *)
  | Match of (relv * tm * (id * tm) option) list * tm option * cls
  | Absurd
  (* magic *)
  | Magic

and tms = tm list

and p =
  | PId of id
  | PMul of id * ps
  | PAdd of id * int * ps

and ps = p list
and cl = ps * tm
and cls = cl list

type dcl =
  | DTm of
      { name : id
      ; relv : relv
      ; body : (tm * tm) scheme
      }
  | DInd of
      { name : id
      ; relv : relv
      ; body : (tm * dconstrs) param scheme
      }

and dcls = dcl list

and dconstr =
  (* multiplicative constructor *)
  | DMul of id * tele
  (* additive constructor *)
  | DAdd of id * tele

and dconstrs = dconstr list
and 'a scheme = (ids, 'a) binder

and 'a param =
  | PBase of 'a
  | PBind of tm * (id, 'a param) binder

and tele =
  | TBase of tm
  | TBind of relv * tm * (id, tele) binder
