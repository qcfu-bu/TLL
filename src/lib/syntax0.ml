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

type ('a, 'b) binder = Binder of 'a * 'b
[@@deriving show { with_path = false }]

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
  (* custom *)
  | UOpr of id * tm
  | BOpr of id * tm * tm
  | Hole of int
  (* magic *)
  | Magic of tm
[@@deriving show { with_path = false }]

and tms = tm list

and p =
  | PId of id
  | PAbsurd
  | PConstr of id * ps
  | PUOpr of id * p
  | PBOpr of id * p * p
  | PHole of int
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
  | Extern of
      { name : id
      ; relv : relv
      ; body : tm scheme
      ; view : view list
      }
  | Notation of
      { name : id
      ; body : tm
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

let subst_phole map p =
  let rec aux = function
    | PId x -> PId x
    | PAbsurd -> PAbsurd
    | PConstr (id, ps) -> PConstr (id, List.map aux ps)
    | PUOpr (id, p) -> PUOpr (id, aux p)
    | PBOpr (id, p1, p2) -> PBOpr (id, aux p1, aux p2)
    | PHole i -> map.(i - 1)
  in
  aux p

let subst_hole map m =
  let rec aux = function
    (* inference *)
    | Ann (m, n) -> Ann (aux m, aux n)
    | IMeta -> IMeta
    (* core *)
    | Type s -> Type s
    | Id (id, view) -> Id (id, view)
    | Inst (id, ss, view) -> Inst (id, ss, view)
    | Pi (relv, s, a, Binder (id, b)) -> Pi (relv, s, aux a, Binder (id, aux b))
    | Fun (a, Binder (id, cls), view) ->
      let cls = List.map (fun (ps, rhs) -> (ps, Option.map aux rhs)) cls in
      Fun (aux a, Binder (id, cls), view)
    | App ms -> App (List.map aux ms)
    | Let (relv, m, Binder (id, n)) -> Let (relv, aux m, Binder (id, aux n))
    (* inductive *)
    | Match (ms, a, cls) ->
      let ms =
        List.map
          (fun (relv, m, a) ->
            (relv, aux m, Option.map (fun (id, a) -> (id, aux a)) a))
          ms
      in
      let a = Option.map aux a in
      let cls = List.map (fun (ps, rhs) -> (ps, Option.map aux rhs)) cls in
      Match (ms, a, cls)
    (* monad *)
    | IO a -> IO (aux a)
    | Return m -> Return (aux m)
    | MLet (m, Binder (id, n)) -> MLet (aux m, Binder (id, aux n))
    (* custom *)
    | UOpr (sym, m) -> UOpr (sym, aux m)
    | BOpr (sym, m, n) -> BOpr (sym, aux m, aux n)
    | Hole i -> map.(i - 1)
    (* magic *)
    | Magic a -> Magic (aux a)
  in
  aux m
