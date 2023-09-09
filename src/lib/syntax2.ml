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
  (* primitive terms *)
  | Int of int
  | Char of char
  | String of string
  (* primitive operators *)
  | Neg of tm (* int -> int *)
  | Add of tm * tm (* int -> int -> int *)
  | Sub of tm * tm (* int -> int -> int *)
  | Mul of tm * tm (* int -> int -> int *)
  | Div of tm * tm (* int -> int -> int *)
  | Mod of tm * tm (* int -> int -> int *)
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
  (* primitive effects *)
  | Print of tm (* string -> IO unit *)
  | Prerr of tm (* string -> IO unit *)
  | ReadLn of tm (* unit -> IO string *)
  | Fork of tm (* (ch P1 -> IO unit) -> IO (ch P2) *)
  | Send of relv * sort * tm (* ch P1 -> m -> IO (ch P2) *)
  | Recv of relv * sort * tm (* ch P1 -> IO (exists m, ch P1) *)
  | Close of bool * tm (* ch end -> IO unit *)
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

(* primitive terms *)
let _Int i = box (Int i)
let _Char c = box (Char c)
let _String s = box (String s)

(* primitive operators *)
let _Neg = box_apply (fun m -> Neg m)
let _Add = box_apply2 (fun m n -> Add (m, n))
let _Sub = box_apply2 (fun m n -> Sub (m, n))
let _Mul = box_apply2 (fun m n -> Mul (m, n))
let _Div = box_apply2 (fun m n -> Div (m, n))
let _Mod = box_apply2 (fun m n -> Mod (m, n))
let _Lte = box_apply2 (fun m n -> Lte (m, n))
let _Gte = box_apply2 (fun m n -> Gte (m, n))
let _Lt = box_apply2 (fun m n -> Lt (m, n))
let _Gt = box_apply2 (fun m n -> Gt (m, n))
let _Eq = box_apply2 (fun m n -> Eq (m, n))
let _Chr = box_apply (fun m -> Chr m)
let _Ord = box_apply (fun m -> Ord m)
let _Push = box_apply2 (fun m n -> Push (m, n))
let _Cat = box_apply2 (fun m n -> Cat (m, n))
let _Size = box_apply (fun m -> Size m)
let _Indx = box_apply2 (fun m n -> Indx (m, n))

(* primitive effects *)
let _Print = box_apply (fun m -> Print m)
let _Prerr = box_apply (fun m -> Prerr m)
let _ReadLn = box_apply (fun m -> ReadLn m)
let _Fork = box_apply (fun m -> Fork m)
let _Send relv role = box_apply (fun m -> Send (relv, role, m))
let _Recv relv role = box_apply (fun m -> Recv (relv, role, m))
let _Close role = box_apply (fun m -> Close (role, m))

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
    let cls = List.map (fun (c, bnd) -> _PConstr c (box_mbinder lift_tm bnd)) cls in
    _Match relv s (lift_tm m) (box_list cls)
  | Absurd -> _Absurd
  (* monad *)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* primitive terms *)
  | Int i -> _Int i
  | Char c -> _Char c
  | String s -> _String s
  (* primitive operators *)
  | Neg m -> _Neg (lift_tm m)
  | Add (m, n) -> _Add (lift_tm m) (lift_tm n)
  | Sub (m, n) -> _Sub (lift_tm m) (lift_tm n)
  | Mul (m, n) -> _Mul (lift_tm m) (lift_tm n)
  | Div (m, n) -> _Div (lift_tm m) (lift_tm n)
  | Mod (m, n) -> _Mod (lift_tm m) (lift_tm n)
  | Lte (m, n) -> _Lte (lift_tm m) (lift_tm n)
  | Gte (m, n) -> _Gte (lift_tm m) (lift_tm n)
  | Lt (m, n) -> _Lt (lift_tm m) (lift_tm n)
  | Gt (m, n) -> _Gt (lift_tm m) (lift_tm n)
  | Eq (m, n) -> _Eq (lift_tm m) (lift_tm n)
  | Chr m -> _Chr (lift_tm m)
  | Ord m -> _Ord (lift_tm m)
  | Push (m, n) -> _Push (lift_tm m) (lift_tm n)
  | Cat (m, n) -> _Cat (lift_tm m) (lift_tm n)
  | Size m -> _Size (lift_tm m)
  | Indx (m, n) -> _Indx (lift_tm m) (lift_tm n)
  (* primitive effects *)
  | Print m -> _Print (lift_tm m)
  | Prerr m -> _Prerr (lift_tm m)
  | ReadLn m -> _ReadLn (lift_tm m)
  | Fork m -> _Fork (lift_tm m)
  | Send (role, s, m) -> _Send role s (lift_tm m)
  | Recv (role, s, m) -> _Recv role s (lift_tm m)
  | Close (role, m) -> _Close role (lift_tm m)
  (* erasure *)
  | NULL -> _NULL
  (* magic *)
  | Magic -> _Magic
