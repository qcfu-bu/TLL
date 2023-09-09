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
  | Let of relv * tm * (p, tm) binder
  (* inductive *)
  | Match of (relv * tm * (id * tm) option) list * tm option * cls
  (* monad *)
  | IO of tm
  | Return of tm
  | MLet of tm * (p, tm) binder
  (* custom *)
  | UOpr of id * tm
  | BOpr of id * tm * tm
  | Hole of int
  (* pimitive types *)
  | Int_t
  | Char_t
  | String_t
  (* pimitive terms *)
  | Int of int
  | Char of char
  | String of string
  (* primitive operators *)
  | Neg of tm (* int -> int *)
  | Add of tm * tm (* int -> int -> int *)
  | Sub of tm * tm (* int -> int -> int *)
  | Mul of tm * tm (* int -> int -> int *)
  | Div of tm * tm (* int -> int -> int *)
  | Rem of tm * tm (* int -> int -> int *)
  | Lte of tm * tm (* int -> int -> bool *)
  | Gte of tm * tm (* int -> int -> bool *)
  | Lt of tm * tm (* int -> int -> bool *)
  | Gt of tm * tm (* int -> int -> bool *)
  | Eq of tm * tm (* int -> int -> bool *)
  | Chr of tm (* int -> char *)
  | Ord of tm (* char -> int *)
  | Push of tm * tm (* string -> char -> string *)
  | Cat of tm * tm (* string -> string -> string *)
  | Size of tm (* string -> int *)
  | Indx of tm * tm (* string -> int -> char *)
  (* primitive sessions *)
  | Proto
  | End
  | Act of relv * bool * tm * (id, tm) binder
  | Ch of bool * tm
  (* primitive effects *)
  | Print of tm (* string -> IO unit *)
  | Prerr of tm (* string -> IO unit *)
  | ReadLn of tm (* unit -> IO string *)
  | Fork of tm (* (ch P1 -> IO unit) -> IO (ch P2) *)
  | Send of tm (* ch P1 -> m -> IO (ch P2) *)
  | Recv of tm (* ch P1 -> IO (exists m, ch P1) *)
  | Close of tm (* ch end -> IO unit *)
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
      ; body : (tm option * tm) scheme
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
    (* pimitive types *)
    | Int_t -> Int_t
    | Char_t -> Char_t
    | String_t -> String_t
    (* pimitive terms *)
    | Int i -> Int i
    | Char c -> Char c
    | String s -> String s
    (* primitive operators *)
    | Neg m -> Neg (aux m)
    | Add (m, n) -> Add (aux m, aux n)
    | Sub (m, n) -> Sub (aux m, aux n)
    | Mul (m, n) -> Mul (aux m, aux n)
    | Div (m, n) -> Div (aux m, aux n)
    | Rem (m, n) -> Rem (aux m, aux n)
    | Lte (m, n) -> Lte (aux m, aux n)
    | Gte (m, n) -> Gte (aux m, aux n)
    | Lt (m, n) -> Lt (aux m, aux n)
    | Gt (m, n) -> Gt (aux m, aux n)
    | Eq (m, n) -> Eq (aux m, aux n)
    | Chr m -> Chr (aux m)
    | Ord m -> Ord (aux m)
    | Push (m, n) -> Push (aux m, aux n)
    | Cat (m, n) -> Cat (aux m, aux n)
    | Size m -> Size (aux m)
    | Indx (m, n) -> Indx (aux m, aux n)
    (* primitive sessions *)
    | Proto -> Proto
    | End -> End
    | Act (relv, role, a, Binder (id, n)) ->
      Act (relv, role, aux a, Binder (id, aux n))
    | Ch (role, m) -> Ch (role, aux m)
    (* primitive effects *)
    | Print m -> Print (aux m)
    | Prerr m -> Prerr (aux m)
    | ReadLn tm -> ReadLn (aux m)
    | Fork m -> Fork (aux m)
    | Send m -> Send (aux m) 
    | Recv m -> Recv (aux m)
    | Close m -> Close (aux m)
    (* custom *)
    | UOpr (sym, m) -> UOpr (sym, aux m)
    | BOpr (sym, m, n) -> BOpr (sym, aux m, aux n)
    | Hole i -> map.(i - 1)
    (* magic *)
    | Magic a -> Magic (aux a)
  in
  aux m
