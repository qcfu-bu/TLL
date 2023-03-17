open Fmt
open Bindlib
open Names

(* syntax definitions *)
type sort = U | L
type rel = N | R
type role = Pos | Neg
type prim = Stdin | Stdout | Stderr

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
  | Rew of (tm, tm) binder * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* session *)
  | Proto
  | End of role
  | Act of rel * role * tm * (tm, tm) binder
  | Ch of role * tm
  | Open of prim
  | Fork of tm * (tm, tm) binder
  | Recv of rel * tm
  | Send of rel * tm
  | Close of tm

and tms = tm array

and cl =
  | PPair of rel * sort * (tm, tm) mbinder
  | PCons of C.t * (tm, tm) mbinder

and cls = cl array

type dcl = DTm of rel * tm var * tm * tm | DData of D.t * tm param * dconss
and dcls = dcl list
and dcons = DCons of C.t * tele param
and dconss = dcons list
and 'a param = PBase of 'a | PBind of tm * (tm, 'a param) binder
and tele = TBase of tm | TBind of rel * tm * (tm, tele) binder

(* variable set/map *)
module VSet = Set.Make (struct
  type t = tm var

  let compare = compare_vars
end)

module VMap = Map.Make (struct
  type t = tm var

  let compare = compare_vars
end)

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
let _End rol = box (End rol)
let _Act rel rol = box_apply2 (fun a bnd -> Act (rel, rol, a, bnd))
let _Ch rol = box_apply (fun a -> Ch (rol, a))
let _Open prim = box (Open prim)
let _Fork = box_apply2 (fun a bnd -> Fork (a, bnd))
let _Recv rel = box_apply (fun m -> Recv (rel, m))
let _Send rel = box_apply (fun m -> Send (rel, m))
let _Close = box_apply (fun m -> Close m)

(* cl *)
let _PPair rel s = box_apply (fun bnd -> PPair (rel, s, bnd))
let _PCons c = box_apply (fun bnd -> PCons (c, bnd))

(* param *)
let _PBase a = box_apply (fun a -> PBase a) a
let _PBind a bnd = box_apply2 (fun a bnd -> PBind (a, bnd)) a bnd

(* tele *)
let _TBase = box_apply (fun a -> TBase a)
let _TBind rel = box_apply2 (fun a bnd -> TBind (rel, a, bnd))

(* lifting *)
let rec lift = function
  (* inference *)
  | Ann (m, a) -> _Ann (lift m) (lift a)
  | Meta (x, ms) ->
      let ms = Array.map lift ms in
      _Meta x (box_array ms)
  (* core *)
  | Type s -> _Type s
  | Var x -> _Var x
  | Pi (rel, s, a, bnd) -> _Pi rel s (lift a) (box_binder lift bnd)
  | Lam (rel, s, bnd) -> _Lam rel s (box_binder lift bnd)
  | App (m, n) -> _App (lift m) (lift n)
  | Let (rel, m, bnd) -> _Let rel (lift m) (box_binder lift bnd)
  | Fix (x, bnd) -> _Fix x (box_binder lift bnd)
  (* data *)
  | Sigma (rel, s, a, bnd) -> _Sigma rel s (lift a) (box_binder lift bnd)
  | Pair (rel, s, m, n) -> _Pair rel s (lift m) (lift n)
  | Data (d, ms) ->
      let ms = Array.map lift ms in
      _Data d (box_array ms)
  | Cons (c, ms) ->
      let ms = Array.map lift ms in
      _Cons c (box_array ms)
  | Match (m, bnd, cls) ->
      let cls =
        Array.map
          (function
            | PPair (rel, s, bnd) -> _PPair rel s (box_mbinder lift bnd)
            | PCons (c, bnd) -> _PCons c (box_mbinder lift bnd))
          cls
      in
      _Match (lift m) (box_binder lift bnd) (box_array cls)
  (* equality *)
  | Eq (m, n) -> _Eq (lift m) (lift n)
  | Refl -> _Refl
  | Rew (bnd, pf, m) -> _Rew (box_binder lift bnd) (lift pf) (lift m)
  (* monadic *)
  | IO a -> _IO (lift a)
  | Return m -> _Return (lift m)
  | MLet (m, bnd) -> _MLet (lift m) (box_binder lift bnd)
  (* session *)
  | Proto -> _Proto
  | End rol -> _End rol
  | Act (rel, rol, a, bnd) -> _Act rel rol (lift a) (box_binder lift bnd)
  | Ch (rol, m) -> _Ch rol (lift m)
  | Open prim -> _Open prim
  | Fork (a, bnd) -> _Fork (lift a) (box_binder lift bnd)
  | Recv (rel, m) -> _Recv rel (lift m)
  | Send (rel, m) -> _Send rel (lift m)
  | Close m -> _Close (lift m)

(* utility *)
let _mLam rel s xs m =
  List.fold_right (fun x m -> _Lam rel s (bind_var x m)) xs m

let mkApps hd ms = List.fold_left (fun hd m -> App (hd, m)) hd ms

let unApps m =
  let rec aux m ns =
    match m with App (m, n) -> aux m (n :: ns) | _ -> (m, ns)
  in
  aux m []
