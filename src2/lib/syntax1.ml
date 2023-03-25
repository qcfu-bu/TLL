open Fmt
open Bindlib
open Names

(* syntax definitions *)
type sort =
  | U
  | L

type rel =
  | N
  | R

type role =
  | Pos
  | Neg

type prim =
  | Stdin
  | Stdout
  | Stderr

type tm =
  (* inference *)
  | Ann of tm * tm
  | Meta of M.t * tms
  (* core *)
  | Type of sort
  | Var of tm var
  | Pi of rel * sort * tm * (tm, tm) binder
  | Lam of rel * sort * (tm, tm) binder
  | App of tm * tm
  | Let of rel * tm * (tm, tm) binder
  | Fix of tm var * (tm, tm) binder
  (* data *)
  | Sigma of rel * sort * tm * (tm, tm) binder
  | Pair of rel * sort * tm * tm
  | Data of D.t * tms
  | Cons of C.t * tms
  | Match of tm * (tm, tm) binder * cls
  (* equality *)
  | Eq of tm * tm
  | Refl
  | Rew of (tm, tm) mbinder * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* session *)
  | Proto
  | End
  | Act of rel * role * tm * (tm, tm) binder
  | Ch of role * tm
  | Open of prim
  | Fork of tm * (tm, tm) binder
  | Recv of tm
  | Send of tm
  | Close of tm

and tms = tm list

and cl =
  | PPair of rel * sort * (tm, tm) mbinder
  | PCons of C.t * (tm, tm) mbinder

and cls = cl list

type dcl =
  | DTm of rel * tm var * tm * tm
  | DData of D.t * tm param * dconss

and dcls = dcl list
and dcons = DCons of C.t * tele param
and dconss = dcons list

and 'a param =
  | PBase of 'a
  | PBind of tm * (tm, 'a param) binder

and tele =
  | TBase of tm
  | TBind of rel * tm * (tm, tele) binder

(* variable set/map *)
module V = struct
  type t = tm var

  let compare = compare_vars
  let pp fmt x = pf fmt "%s" (name_of x)
end

module VSet = Set.Make (V)
module VMap = Map.Make (V)

(* smart constructors *)
let mk = new_var (fun x -> Var x)

(* sort *)
let _U = box U
let _L = box L

(* rel *)
let _N = box N
let _R = box R

(* role *)
let _Pos = box Pos
let _Neg = box Neg

(* prim *)
let _Stdin = box Stdin
let _Stdout = box Stdout
let _Stderr = box Stderr

(* inference *)
let _Ann = box_apply2 (fun m a -> Ann (m, a))
let _Meta x = box_apply (fun ms -> Meta (x, ms))

(* core *)
let _Type s = box (Type s)
let _Var = box_var
let _Pi rel s = box_apply2 (fun a bnd -> Pi (rel, s, a, bnd))
let _Lam rel s = box_apply (fun bnd -> Lam (rel, s, bnd))
let _App = box_apply2 (fun m n -> App (m, n))
let _Let rel = box_apply2 (fun m bnd -> Let (rel, m, bnd))
let _Fix x = box_apply (fun bnd -> Fix (x, bnd))

(* data *)
let _Sigma rel s = box_apply2 (fun a bnd -> Sigma (rel, s, a, bnd))
let _Pair rel s = box_apply2 (fun m n -> Pair (rel, s, m, n))
let _Data d = box_apply (fun ms -> Data (d, ms))
let _Cons c = box_apply (fun ms -> Cons (c, ms))
let _Match = box_apply3 (fun m bnd cls -> Match (m, bnd, cls))

(* equality *)
let _Eq = box_apply2 (fun m n -> Eq (m, n))
let _Refl = box Refl
let _Rew = box_apply3 (fun bnd pf m -> Rew (bnd, pf, m))

(* monadic *)
let _IO = box_apply (fun a -> IO a)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m bnd -> MLet (m, bnd))

(* session *)
let _Proto = box Proto
let _End = box End
let _Act rel rol = box_apply2 (fun a bnd -> Act (rel, rol, a, bnd))
let _Ch rol = box_apply (fun a -> Ch (rol, a))
let _Open prim = box (Open prim)
let _Fork = box_apply2 (fun a bnd -> Fork (a, bnd))
let _Recv = box_apply (fun m -> Recv m)
let _Send = box_apply (fun m -> Send m)
let _Close = box_apply (fun m -> Close m)

(* cl *)
let _PPair rel s = box_apply (fun bnd -> PPair (rel, s, bnd))
let _PCons c = box_apply (fun bnd -> PCons (c, bnd))

(* dcl *)
let _DTm rel x = box_apply2 (fun a m -> DTm (rel, x, a, m))
let _DData d = box_apply2 (fun ptm dconss -> DData (d, ptm, dconss))

(* dcons *)
let _DCons c = box_apply (fun ptl -> DCons (c, ptl))

(* param *)
let _PBase a = box_apply (fun a -> PBase a) a
let _PBind a bnd = box_apply2 (fun a bnd -> PBind (a, bnd)) a bnd

(* tele *)
let _TBase = box_apply (fun a -> TBase a)
let _TBind rel = box_apply2 (fun a bnd -> TBind (rel, a, bnd))

(* lifting *)
let rec lift_tm = function
  (* inference *)
  | Ann (m, a) -> _Ann (lift_tm m) (lift_tm a)
  | Meta (x, ms) ->
    let ms = List.map lift_tm ms in
    _Meta x (box_list ms)
  (* core *)
  | Type s -> _Type s
  | Var x -> _Var x
  | Pi (rel, s, a, bnd) -> _Pi rel s (lift_tm a) (box_binder lift_tm bnd)
  | Lam (rel, s, bnd) -> _Lam rel s (box_binder lift_tm bnd)
  | App (m, n) -> _App (lift_tm m) (lift_tm n)
  | Let (rel, m, bnd) -> _Let rel (lift_tm m) (box_binder lift_tm bnd)
  | Fix (x, bnd) -> _Fix x (box_binder lift_tm bnd)
  (* data *)
  | Sigma (rel, s, a, bnd) -> _Sigma rel s (lift_tm a) (box_binder lift_tm bnd)
  | Pair (rel, s, m, n) -> _Pair rel s (lift_tm m) (lift_tm n)
  | Data (d, ms) ->
    let ms = List.map lift_tm ms in
    _Data d (box_list ms)
  | Cons (c, ms) ->
    let ms = List.map lift_tm ms in
    _Cons c (box_list ms)
  | Match (m, bnd, cls) ->
    let cls =
      List.map
        (function
          | PPair (rel, s, bnd) -> _PPair rel s (box_mbinder lift_tm bnd)
          | PCons (c, bnd) -> _PCons c (box_mbinder lift_tm bnd))
        cls
    in
    _Match (lift_tm m) (box_binder lift_tm bnd) (box_list cls)
  (* equality *)
  | Eq (m, n) -> _Eq (lift_tm m) (lift_tm n)
  | Refl -> _Refl
  | Rew (bnd, pf, m) -> _Rew (box_mbinder lift_tm bnd) (lift_tm pf) (lift_tm m)
  (* monadic *)
  | IO a -> _IO (lift_tm a)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* session *)
  | Proto -> _Proto
  | End -> _End
  | Act (rel, rol, a, bnd) -> _Act rel rol (lift_tm a) (box_binder lift_tm bnd)
  | Ch (rol, m) -> _Ch rol (lift_tm m)
  | Open prim -> _Open prim
  | Fork (a, bnd) -> _Fork (lift_tm a) (box_binder lift_tm bnd)
  | Recv m -> _Recv (lift_tm m)
  | Send m -> _Send (lift_tm m)
  | Close m -> _Close (lift_tm m)

let rec lift_param lift = function
  | PBase a -> _PBase (lift a)
  | PBind (a, bnd) -> _PBind (lift_tm a) (box_binder (lift_param lift) bnd)

let rec lift_tele = function
  | TBase a -> _TBase (lift_tm a)
  | TBind (rel, a, bnd) -> _TBind rel (lift_tm a) (box_binder lift_tele bnd)

let lift_dcons (DCons (c, ptl)) = _DCons c (lift_param lift_tele ptl)
let lift_dconss dconss = box_list (List.map lift_dcons dconss)

let lift_dcl = function
  | DTm (rel, x, a, m) -> _DTm rel x (lift_tm a) (lift_tm m)
  | DData (d, ptm, dconss) ->
    _DData d (lift_param lift_tm ptm) (lift_dconss dconss)

let lift_dcls dcls = box_list (List.map lift_dcl dcls)

(* utility *)
let _mLam rel s xs m =
  List.fold_right (fun x m -> _Lam rel s (bind_var x m)) xs m

let _mkApps hd ms = List.fold_left _App hd ms
let mkApps hd ms = List.fold_left (fun hd m -> App (hd, m)) hd ms

let unApps m =
  let rec aux m ns =
    match m with
    | App (m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []
