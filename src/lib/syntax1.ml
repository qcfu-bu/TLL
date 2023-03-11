(* open Fmt *)
open Names

type sort = U | L
[@@deriving show { with_path = false }]

type rel = N | R
[@@deriving show { with_path = false }]

type ('a, 'b) abs = Abs of 'a * 'b
[@@deriving show { with_path = false }]

type role = Pos | Neg
[@@deriving show { with_path = false }]

type tm =
  (* inference *)
  | Ann of tm * tm
  | Meta of M.t * tms
  (* core *)
  | Type of sort
  | Var of V.t
  | Pi of rel * sort * tm * (V.t, tm) abs
  | Lam of rel * sort * (V.t, tm) abs
  | App of tm * tm
  | Let of rel * tm * (V.t, tm) abs
  | Fix of (V.t, tm) abs
  (* data *)
  | Sig of rel * sort * tm * (V.t, tm) abs
  | Pair of rel * sort * tm * tm
  | Data of D.t * tms
  | Cons of C.t * tms
  | Match of tm * mot * cls
  (* equality *)
  | Eq of tm * tm
  | Refl of tm
  | EqElim of
      (V.t, (V.t, tm) abs) abs * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | Bind of tm * (V.t, tm) abs
  (* session *)
  | Proto
  | End of role
  | Act of rel * role * tm * (V.t, tm) abs
  | Ch of role * tm
  | Fork of tm * (V.t, tm) abs
  | Recv of rel * tm
  | Send of rel * tm
  | Close of tm
  (* effectful *)
  | Read of tm
  | Print of tm
  | Ptr of tm * tm
  | Cap of tm * tm
  | PtrElim of
      (V.t, (V.t, tm) abs) abs *
      (V.t, (V.t, tm) abs) abs * tm
  | Alloc of tm
  | Get of tm * tm
  | Set of tm * tm * tm
  | Free of tm * tm

and tms = tm list
and tm_opt = tm option

and mot = 
  | Mot0
  | Mot1 of (V.t, tm) abs
  | Mot2 of (p, tm) abs
  | Mot3 of (V.t, (p, tm) abs) abs

and p =
  | PVar of V.t
  | PPair of V.t * V.t
  | PData of D.t * V.t list
  | PCons of C.t * V.t list

and ps = p list
and cl = (p, tm) abs
and cls = cl list
[@@deriving show { with_path = false }]

type dcl =
  | DTm of rel * V.t * tm_opt * tm
  | DData of D.t * tl * dconss

and dcls = dcl list
and dcons = DCons of C.t * tl
and dconss = dcons list

and tl =
  | TBase of tm
  | TBind of rel * tm * (V.t, tl) abs
[@@deriving show { with_path = false }]


let var x = Var x

let freshen_p = function
  | PVar x -> PVar (V.freshen x)
  | PPair (x, y) -> PPair (V.freshen x, V.freshen y)
  | PData (d, xs) -> PData (d, List.map V.freshen xs)
  | PCons (c, xs) -> PCons (c, List.map V.freshen xs)

let xs_of_p = function
  | PVar x -> [ x ]
  | PPair (x, y) -> [x; y]
  | PData (_, xs) -> xs
  | PCons (_, xs) -> xs

let findi_opt f ls =
  let rec aux k = function
    | [] -> None
    | h :: t ->
      if f k h then
        Some (k, h)
      else
        aux (k + 1) t
  in
  aux 0 ls

let bindn_tm k xs m =
  let rec aux k = function
    (* inference *)
    | Ann (a, m) ->
      let a = aux k a in
      let m = aux k m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    (* core *)
    | Type s -> Type s
    | Var y ->
      (let opt = findi_opt (fun _ x -> V.equal x y) xs in
       match opt with
       | Some (i, _) -> Var (V.bind (i + k))
       | None -> Var y)
    | Pi (rel, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (rel, s, a, Abs (x, b))
    | Lam (rel, s, Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (rel, s, Abs (x, m))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (rel, m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (rel, m, Abs (x, n))
    | Fix (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Fix (Abs (x, m))
    (* data *)
    | Sig (rel, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Sig (rel, s, a, Abs (x, b))
    | Pair (rel, s, m, n) ->
      let m = aux k m in
      let n = aux k n in
      Pair (rel, s, m, n)
    | Data (d, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Match (m, mot, cls) ->
      let m = aux k m in
      let mot = aux_mot k mot in
      let cls = 
        List.map
          (fun (Abs (p, m)) ->
             let xs = xs_of_p p in
             let k = k + List.length xs in
             let m = aux k m in
             Abs (p, m))
          cls
      in
      Match (m, mot, cls)
    (* equality *)
    | Eq (m, n) ->
      let m = aux k m in
      let n = aux k n in
      Eq (m, n)
    | Refl m -> Refl (aux k m)
    | EqElim (Abs (x, Abs (y, c)), h, p) ->
      let c = aux (k + 2) c in
      let h = aux k h in
      let p = aux k p in
      EqElim (Abs (x, Abs (y, c)), h, p)
    (* monadic *)
    | IO a -> IO (aux k a)
    | Return m -> Return (aux k m)
    | Bind (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Bind (m, Abs (x, n))
    (* session *)
    | Proto -> Proto
    | End rol -> End rol
    | Act (rel, rol, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (rel, rol, a, Abs (x, b))
    | Ch (rol, a) -> Ch (rol, aux k a)
    | Fork (a, Abs (x, m)) ->
      let a = aux k a in
      let m = aux (k + 1) m in
      Fork (a, Abs (x, m))
    | Recv (rel, m) -> Recv (rel, aux k m)
    | Send (rel, m) -> Send (rel, aux k m)
    | Close m -> Close (aux k m)
    (* effectful *)
    | Read m -> Read (aux k m)
    | Print m -> Print (aux k m)
    | Ptr (l, a) -> Ptr (l, aux k a)
    | Cap (l, m) -> Cap (l, aux k m)
    | PtrElim (Abs (x1, Abs (y1, a)),
               Abs (x2, Abs (y2, n)), c) ->
      let a = aux (k + 2) a in
      let n = aux (k + 2) n in
      let c = aux k c in
      PtrElim (Abs (x1, Abs (y1, a)),
               Abs (x2, Abs (y2, n)), c)
    | Alloc m -> Alloc (aux k m)
    | Get (l, c) ->
      let l = aux k l in
      let c = aux k c  in
      Get (l, c)
    | Set (l, c, m) ->
      let l = aux k l in
      let c = aux k c in
      let m = aux k m in
      Set (l, c, m)
    | Free (l, c) ->
      let l = aux k l in
      let c = aux k c in
      Free (l, c)
  and aux_mot k = function
    | Mot0 -> Mot0
    | Mot1 (Abs (x, a)) ->
      let a = aux (k + 1) a in
      Mot1 (Abs (x, a))
    | Mot2 (Abs (p, a)) ->
      let xs = xs_of_p p in
      let k = k + List.length xs in
      let a = aux k a in
      Mot2 (Abs (p, a))
    | Mot3 (Abs (x, Abs (p, a))) ->
      let xs = xs_of_p p in
      let k = k + 1 + List.length xs in
      let a = aux k a in
      Mot3 (Abs (x, Abs (p, a)))
  in
  aux k m

let unbindn_tm k xs m =
  let sz = List.length xs in
  let rec aux k = function
    (* inference *)
    | Ann (a, m) ->
      let a = aux k a in
      let m = aux k m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    (* core *)
    | Type s -> Type s
    | Var y ->
      (match V.is_bound y sz k with
       | Some i -> List.nth xs (i - k)
       | None -> Var y)
    | Pi (rel, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (rel, s, a, Abs (x, b))
    | Lam (rel, s, Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (rel, s, Abs (x, m))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (rel, m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (rel, m, Abs (x, n))
    | Fix (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Fix (Abs (x, m))
    (* data *)
    | Sig (rel, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Sig (rel, s, a, Abs (x, b))
    | Pair (rel, s, m, n) ->
      let m = aux k m in
      let n = aux k n in
      Pair (rel, s, m, n)
    | Data (d, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Match (m, mot, cls) ->
      let m = aux k m in
      let mot = aux_mot k mot in
      let cls = 
        List.map 
          (fun (Abs (p, m)) ->
             let xs = xs_of_p p in
             let k = k + List.length xs in
             let m = aux k m in
             Abs (p, m))
          cls
      in
      Match (m, mot, cls)
    (* equality *)
    | Eq (m, n) ->
      let m = aux k m in
      let n = aux k n in
      Eq (m, n)
    | Refl m -> Refl (aux k m)
    | EqElim (Abs (x, Abs (y, c)), h, p) ->
      let c = aux (k + 2) c in
      let h = aux k h in
      let p = aux k p in
      EqElim (Abs (x, Abs (y, c)), h, p)
    (* monadic *)
    | IO a -> IO (aux k a)
    | Return m -> Return (aux k m)
    | Bind (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Bind (m, Abs (x, n))
    (* session *)
    | Proto -> Proto
    | End rol -> End rol
    | Act (rel, rol, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (rel, rol, a, Abs (x, b))
    | Ch (rol, a) -> Ch (rol, aux k a)
    | Fork (a, Abs (x, m)) ->
      let a = aux k a in
      let m = aux (k + 1) m in
      Fork (a, Abs (x, m))
    | Recv (rel, m) -> Recv (rel, aux k m)
    | Send (rel, m) -> Send (rel, aux k m)
    | Close m -> Close (aux k m)
    (* effectful *)
    | Read m -> Read (aux k m)
    | Print m -> Print (aux k m)
    | Ptr (l, a) -> Ptr (l, aux k a)
    | Cap (l, m) -> Cap (l, aux k m)
    | PtrElim (Abs (x1, Abs (y1, a)),
               Abs (x2, Abs (y2, n)), c) ->
      let a = aux (k + 2) a in
      let n = aux (k + 2) n in
      let c = aux k c in
      PtrElim (Abs (x1, Abs (y1, a)),
               Abs (x2, Abs (y2, n)), c)
    | Alloc m -> Alloc (aux k m)
    | Get (l, c) ->
      let l = aux k l in
      let c = aux k c  in
      Get (l, c)
    | Set (l, c, m) ->
      let l = aux k l in
      let c = aux k c in
      let m = aux k m in
      Set (l, c, m)
    | Free (l, c) ->
      let l = aux k l in
      let c = aux k c in
      Free (l, c)
  and aux_mot k = function
    | Mot0 -> Mot0
    | Mot1 (Abs (x, a)) ->
      let a = aux (k + 1) a in
      Mot1 (Abs (x, a))
    | Mot2 (Abs (p, a)) ->
      let xs = xs_of_p p in
      let k = k + List.length xs in
      let a = aux k a in
      Mot2 (Abs (p, a))
    | Mot3 (Abs (x, Abs (p, a))) ->
      let xs = xs_of_p p in
      let k = k + 1 + List.length xs in
      let a = aux k a in
      Mot3 (Abs (x, Abs (p, a)))
  in
  aux k m
