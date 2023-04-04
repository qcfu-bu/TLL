open Fmt
open Bindlib
open Names

type sort =
  | U
  | L

type role =
  | Pos
  | Neg

type prim =
  | Stdin
  | Stdout
  | Stderr

type tm =
  (* core *)
  | Var of tm var
  | Const of I.t
  | Lam of (tm, tm) binder
  | App of sort * tm * tm
  | Let of tm * (tm, tm) binder
  (* data *)
  | Pair of tm * tm
  | Cons of C.t * tms
  | Match of sort * tm * cls
  (* monadic *)
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* session *)
  | Open of prim
  | Fork of (tm, tm) binder
  | Recv of tm
  | Send of tm
  | Close of role * tm
  (* erasure *)
  | Null

and tms = tm list

and cl =
  | PPair of (tm, tm) mbinder
  | PCons of C.t * (tm, tm) mbinder

and cls = cl list

type dcl =
  | DTm of I.t * tm
  | DData of D.t * dconss

and dcons = DCons of C.t * int
and dconss = dcons list

module V = struct
  type t = tm var

  let mk = new_var (fun x -> Var x)
  let compare = compare_vars
  let pp fmt x = pf fmt "%s_v%d" (name_of x) (uid_of x)
end

(* smart constructors *)
let var x = Var x

(* sort *)
let _U = box U
let _L = box L

(* role *)
let _Pos = box Pos
let _Neg = box Neg

(* prim *)
let _Stdin = box Stdin
let _Stdout = box Stdout
let _Stderr = box Stderr

(* core *)
let _Var = box_var
let _Const x = box (Const x)
let _Lam = box_apply (fun bnd -> Lam bnd)
let _App s = box_apply2 (fun m n -> App (s, m, n))
let _Let = box_apply2 (fun m bnd -> Let (m, bnd))

(* data *)
let _Pair = box_apply2 (fun m n -> Pair (m, n))
let _Cons c = box_apply (fun ms -> Cons (c, ms))
let _Match s = box_apply2 (fun m cls -> Match (s, m, cls))

(* monadic *)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m bnd -> MLet (m, bnd))

(* session *)
let _Open prim = box (Open prim)
let _Fork = box_apply (fun bnd -> Fork bnd)
let _Recv = box_apply (fun m -> Recv m)
let _Send = box_apply (fun m -> Send m)
let _Close rol = box_apply (fun m -> Close (rol, m))

(* erasure *)
let _Null = box Null

(* cl *)
let _PPair = box_apply (fun bnd -> PPair bnd)
let _PCons c = box_apply (fun bnd -> PCons (c, bnd))

(* dcl *)
let _DTm x = box_apply (fun m -> DTm (x, m))
let _DData d = box_apply (fun dconss -> DData (d, dconss))

(* dcons *)
let _DCons c i = box (DCons (c, i))

let lift_sort = function
  | U -> _U
  | L -> _L

let rec lift_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Lam bnd -> _Lam (box_binder lift_tm bnd)
  | App (s, m, n) -> _App s (lift_tm m) (lift_tm n)
  | Let (m, bnd) -> _Let (lift_tm m) (box_binder lift_tm bnd)
  (* data *)
  | Pair (m, n) -> _Pair (lift_tm m) (lift_tm n)
  | Cons (c, ms) ->
    let ms = List.map lift_tm ms in
    _Cons c (box_list ms)
  | Match (s, m, cls) ->
    let cls =
      List.map
        (function
          | PPair bnd -> _PPair (box_mbinder lift_tm bnd)
          | PCons (c, bnd) -> _PCons c (box_mbinder lift_tm bnd))
        cls
    in
    _Match s (lift_tm m) (box_list cls)
  (* monadic *)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* session *)
  | Open prim -> _Open prim
  | Fork bnd -> _Fork (box_binder lift_tm bnd)
  | Recv m -> _Recv (lift_tm m)
  | Send m -> _Send (lift_tm m)
  | Close (rol, m) -> _Close rol (lift_tm m)
  (* erasure *)
  | Null -> _Null

let lift_dcons (DCons (c, i)) = _DCons c i
let lift_dconss dconss = box_list (List.map lift_dcons dconss)

let lift_dcl = function
  | DTm (x, m) -> _DTm x (lift_tm m)
  | DData (d, dconss) -> _DData d (lift_dconss dconss)

let lift_dcls dcls = box_list (List.map lift_dcl dcls)
