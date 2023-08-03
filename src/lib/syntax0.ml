type id = string [@@deriving show { with_path = false }]
and ids = id list

type sort =
  | U
  | L
  | SId of id
[@@deriving show { with_path = false }]

and sorts = sort list

type relv =
  | N
  | R
[@@deriving show { with_path = false }]

type ('a, 'b) binder = Binder of 'a * 'b
[@@deriving show { with_path = false }]

type tm =
  (* inference *)
  | Ann of tm * tm
  (* core *)
  | Type of sort
  | Id of id
  | Inst of id * sorts
  | Pi of relv * sort * tm * (id, tm) binder
  | Fun of tm * (id option, cls) binder
  | App of tms
  | Let of relv * tm * (id, tm) binder
  (* inductive *)
  | Match of (relv * tm * (id * tm) option) list * tm option * cls
  (* monad *)
  | IO of tm
  | Return of tm
  | MLet of tm * (id, tm) binder
  (* magic *)
  | Magic of tm
[@@deriving show { with_path = false }]

and tms = tm list

and p =
  | PId of id
  | PAbsurd
  | PMul of id * ps
  | PAdd of id * int * ps
[@@deriving show { with_path = false }]

and ps = p list
and cl = ps * tm option
and cls = cl list

type dcl =
  | Definition of
      { name : id
      ; relv : relv
      ; body : (tm * tm) scheme
      }
  | Inductive of
      { name : id
      ; relv : relv
      ; body : (tele * dconstrs) param scheme
      }
[@@deriving show { with_path = false }]

and dcls = dcl list

and dconstr =
  | DMul of id * tele
  | DAdd of id * tele

and dconstrs = dconstr list
and 'a scheme = (ids, 'a) binder

and 'a param =
  | PBase of 'a
  | PBind of tm * (id, 'a param) binder

and tele =
  | TBase of tm
  | TBind of relv * tm * (id, tele) binder
