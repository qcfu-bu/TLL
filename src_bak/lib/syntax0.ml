type id = string [@@deriving show { with_path = false }]
and ids = id list

type sort =
  | U (* non-linear *)
  | L (* linear *)
  | SId of id
[@@deriving show { with_path = false }]

and sorts = sort list

type relv =
  | N (* irrelevant *)
  | R (* relevant *)
[@@deriving show { with_path = false }]

type view =
  | E (* explicit *)
  | I (* implicit *)
[@@deriving show { with_path = false }]

type ('a, 'b) binder = Binder of 'a * 'b [@@deriving show { with_path = false }]

type tm =
  (* inference *)
  | Ann of tm * tm
  | IMeta
  (* core *)
  | Type of sort
  | Id of id * view
  | Inst of id * sorts * view
  | Pi of relv * sort * tm * (id, tm) binder
  | Fun of tm * (id option, cls) binder * view list
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
  | PConstr of id * ps
[@@deriving show { with_path = false }]

and ps = p list
and cl = ps * tm option
and cls = cl list

type dcl =
  | Definition of
      { name : id
      ; relv : relv
      ; body : (tm * tm) scheme
      ; view : view list
      }
  | Inductive of
      { name : id
      ; relv : relv
      ; body : (tele * dconstrs) param scheme
      ; view : view list
      }
[@@deriving show { with_path = false }]

and dcls = dcl list
and dconstr = DConstr of id * tele * view list
and dconstrs = dconstr list
and 'a scheme = (ids, 'a) binder

and 'a param =
  | PBase of 'a
  | PBind of tm * (id, 'a param) binder

and tele =
  | TBase of tm
  | TBind of relv * tm * (id, tele) binder
