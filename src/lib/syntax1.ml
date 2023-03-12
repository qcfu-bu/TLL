open Fmt
open Names

(* syntax definitions *)

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
  | Srt of S.t
  | Pi of rel * sort * tm * (V.t, tm) abs
  | Lam of rel * sort * (V.t * tm_opt, tm) abs
  | App of tm * tm
  | Let of rel * tm * (V.t * tm_opt, tm) abs
  | Fix of (V.t, tm) abs
  (* data *)
  | Sig of rel * sort * tm * (V.t, tm) abs
  | Pair of rel * sort * tm * tm
  | Data of D.t * s_args * tms
  | Cons of C.t * s_args * tms
  | Match of tm * mot * cls
  (* equality *)
  | Eq of tm * tm
  | Refl of tm
  | EqElim of (V.t * V.t, tm) abs * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | Bind of tm * (V.t * tm_opt, tm) abs
  (* session *)
  | Proto
  | End of role
  | Act of rel * role * tm * (V.t, tm) abs
  | Ch of role * tm
  | Fork of tm * (V.t, tm) abs
  | Recv of rel * tm
  | Send of rel * tm
  | Close of tm
  (* effects *)
  | Read of tm
  | Print of tm

and tms = tm list
and tm_opt = tm option

and mot = 
  | Mot0
  | Mot1 of (V.t, tm) abs
  | Mot2 of (p, tm) abs
  | Mot3 of (V.t * p, tm) abs

and p =
  | PVar of V.t
  | PPair of rel * sort * V.t * V.t
  | PData of D.t * V.t list
  | PCons of C.t * V.t list

and ps = p list
and cl = (p, tm) abs
and cls = cl list

and s_arg = S of sort | M of M.t
and s_args = s_arg list
[@@deriving show { with_path = false }]

type dcl =
  | DTm of rel * V.t * tm_opt * tm
  | DData of D.t * stl * dconss

and dcls = dcl list
and dcons = DCons of C.t * stl
and dconss = dcons list

and stl = SBase of (S.t list, ptl) abs

and ptl =
  | PBase of tl
  | PBind of tm * (V.t, ptl) abs

and tl =
  | TBase of tm
  | TBind of rel * tm * (V.t, tl) abs
[@@deriving show { with_path = false }]

(* utility *)

let var x = Var x

let freshen_p = function
  | PVar x -> PVar (V.freshen x)
  | PPair (rel, s, x, y) -> PPair (rel, s, V.freshen x, V.freshen y)
  | PData (d, xs) -> PData (d, List.map V.freshen xs)
  | PCons (c, xs) -> PCons (c, List.map V.freshen xs)

let xs_of_p = function
  | PVar x -> [ x ]
  | PPair (_, _, x, y) -> [x; y]
  | PData (_, xs) -> xs
  | PCons (_, xs) -> xs

let equal_p p1 p2 =
  match p1, p2 with
  | PVar _, PVar _ -> true
  | PPair (rel1, s1, _, _), PPair (rel2, s2, _, _) ->
    rel1 = rel2 && s1 = s2 
  | PData (d1, xs1), PData (d2, xs2) ->
    D.equal d1 d2 && List.length xs1 = List.length xs2
  | PCons (c1, xs1), PCons (c2, xs2) ->
    C.equal c1 c2 && List.length xs1 = List.length xs2
  | _ -> false

let equal_abs eq (Abs (_, m)) (Abs (_, n)) = eq m n
let equal_ann eq (Abs ((_, a_opt), m)) (Abs ((_, b_opt), n)) =
  match a_opt, b_opt with
  | Some a, Some b ->
    eq a b && eq m n
  | _ -> eq m n
let equal_pabs eq (Abs (p1, m)) (Abs (p2, n)) = equal_p p1 p2 && eq m n

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

(* variable binding/unbinding *)

let bindn_tm k xs m =
  let rec aux k = function
    (* inference *)
    | Ann (m, a) ->
      let m = aux k m in
      let a = aux k a in
      Ann (m, a)
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
    | Srt s -> Srt s
    | Pi (rel, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (rel, s, a, Abs (x, b))
    | Lam (rel, s, Abs ((x, a_opt), m)) ->
      let a_opt = Option.map (aux k) a_opt in
      let m = aux (k + 1) m in
      Lam (rel, s, Abs ((x, a_opt), m))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (rel, m, Abs ((x, a_opt), n)) ->
      let m = aux k m in
      let a_opt = Option.map (aux k) a_opt in
      let n = aux (k + 1) n in
      Let (rel, m, Abs ((x, a_opt), n))
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
    | Data (d, ss, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ss, ms)
    | Cons (c, ss, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ss, ms)
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
    | EqElim (Abs ((x, y), c), h, p) ->
      let c = aux (k + 2) c in
      let h = aux k h in
      let p = aux k p in
      EqElim (Abs ((x, y), c), h, p)
    (* monadic *)
    | IO a -> IO (aux k a)
    | Return m -> Return (aux k m)
    | Bind (m, Abs ((x, a_opt), n)) ->
      let m = aux k m in
      let a_opt = Option.map (aux k) a_opt in
      let n = aux (k + 1) n in
      Bind (m, Abs ((x, a_opt), n))
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
  and aux_mot k = function
    | Mot0 -> Mot0
    | Mot1 (Abs (x, a)) ->
      let a = aux (k + 1) a in
      Mot1 (Abs (x, a))
    | Mot2 (Abs (p, a)) ->
      let k = k + List.length (xs_of_p p) in
      let a = aux k a in
      Mot2 (Abs (p, a))
    | Mot3 (Abs ((x, p), a)) ->
      let k = k + 1 + List.length (xs_of_p p) in
      let a = aux k a in
      Mot3 (Abs ((x, p), a))
  in
  aux k m

let unbindn_tm k xs m =
  let sz = List.length xs in
  let rec aux k = function
    (* inference *)
    | Ann (m, a) ->
      let m = aux k m in
      let a = aux k a in
      Ann (m, a)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    (* core *)
    | Type s -> Type s
    | Var y ->
      (match V.is_bound y sz k with
       | Some i -> List.nth xs (i - k)
       | None -> Var y)
    | Srt s -> Srt s
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
    | Data (d, ss, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ss, ms)
    | Cons (c, ss, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ss, ms)
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
    | EqElim (Abs ((x, y), c), h, p) ->
      let c = aux (k + 2) c in
      let h = aux k h in
      let p = aux k p in
      EqElim (Abs ((x, y), c), h, p)
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
  and aux_mot k = function
    | Mot0 -> Mot0
    | Mot1 (Abs (x, a)) ->
      let a = aux (k + 1) a in
      Mot1 (Abs (x, a))
    | Mot2 (Abs (p, a)) ->
      let k = k + List.length (xs_of_p p) in
      let a = aux k a in
      Mot2 (Abs (p, a))
    | Mot3 (Abs ((x, p), a)) ->
      let k = k + 1 + List.length (xs_of_p p) in
      let a = aux k a in
      Mot3 (Abs ((x, p), a))
  in
  aux k m

let rec bindn_ptl k xs ptl =
  let rec aux k ptl =
    match ptl with
    | PBase tl -> PBase (bindn_tl k xs tl)
    | PBind (a, Abs (x, ptl)) ->
      let a = bindn_tm k xs a in
      let ptl = aux (k + 1) ptl in
      PBind (a, Abs (x, ptl))
  in
  aux k ptl

and bindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase b -> TBase (bindn_tm k xs b)
    | TBind (r, a, Abs (x, tl)) ->
      let a = bindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (r, a, Abs (x, tl))
  in
  aux k tl

let rec unbindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase a -> TBase (unbindn_tm k xs a)
    | TBind (r, a, Abs (x, tl)) ->
      let a = unbindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (r, a, Abs (x, tl))
  in
  aux k tl

let bind_tm x m = Abs (x, bindn_tm 0 [x] m)
let bind_ann x a_opt m = Abs ((x, a_opt), bindn_tm 0 [x] m)
let bind_tm2 x y m = Abs ((x, y), bindn_tm 0 [x; y] m)
let bindp_tm p m =
  let xs = xs_of_p p in
  Abs (p, bindn_tm 0 xs m)
let bindp_tm2 x p m =
  let xs = xs_of_p p in
  Abs ((x, p), bindn_tm 0 (x :: xs) m)
let bind_tl x tl = Abs (x, bindn_tl 0 [x] tl)

let unbind_tm (Abs (x, m)) =
  let x = V.freshen x in
  (x, unbindn_tm 0 [Var x] m)
let unbind_ann (Abs ((x, a_opt), m)) =
  let x = V.freshen x in
  ((x, a_opt), unbindn_tm 0 [Var x] m)
let unbind_tm2 (Abs ((x, y), m)) =
  let x = V.freshen x in
  let y = V.freshen y in
  ((x, y), unbindn_tm 0 [Var x; Var y] m)
let unbindp_tm (Abs (p, m)) =
  let p = freshen_p p in
  let xs = p |> xs_of_p |> List.map var in
  (p, unbindn_tm 0 xs m)
let unbindp_tm2 (Abs ((x, p), m)) =
  let x = V.freshen x in
  let p = freshen_p p in
  let xs = p |> xs_of_p |> List.map var in
  ((x, p), unbindn_tm 0 (Var x :: xs) m)
let unbind_tl (Abs (x, tl)) =
  let x = V.freshen x in
  (x, unbindn_tl 0 [Var x] tl)

let unbind2_tm (Abs (x, m)) (Abs (_, n)) =
  let x = V.freshen x in
  let m = unbindn_tm 0 [Var x] m in
  let n = unbindn_tm 0 [Var x] n in
  (x, m, n)
let unbind2_ann (Abs ((x, a_opt), m)) (Abs ((_, b_opt), n)) =
  let x = V.freshen x in
  let m = unbindn_tm 0 [Var x] m in
  let n = unbindn_tm 0 [Var x] n in
  ((x, a_opt, b_opt), m, n)

let unbindp2_tm (Abs (p1, m)) (Abs (p2, n)) =
  if equal_p p1 p2 then
    let p = freshen_p p1 in
    let xs = p |> xs_of_p |> List.map var in
    let m = unbindn_tm 0 xs m in
    let n = unbindn_tm 0 xs n in
    (p, m, n)
  else
    failwith "unbindp2(%a, %a)" pp_p p1 pp_p p2

(* substitution *)

let asubst_tm (Abs (_, m)) n = unbindn_tm 0 [n] m
let asubst_ann (Abs ((_, _), m)) n = unbindn_tm 0 [n] m
let asubst_tl (Abs (_, tl)) n = unbindn_tl 0 [n] tl

let match_p p m =
  match p, m with
  | PVar _, _ -> [m]
  | PPair (rel1, s1, _, _), Pair (rel2, s2, m, n) ->
    if rel1 = rel2 && s1 = s2 then
      [m; n]
    else
      failwith "match_p"
  | PData (d1, xs), Data (d2, _, ms) ->
    let xs_sz = List.length xs in
    let ms_sz = List.length ms in
    if D.equal d1 d2 && xs_sz = ms_sz then
      ms
    else
      failwith "match_p"
  | PCons (c1, xs), Cons (c2, _, ms) ->
    let xs_sz = List.length xs in
    let ms_sz = List.length ms in
    if C.equal c1 c2 && xs_sz = ms_sz then
      ms
    else
      failwith "match_p"
  | _ -> failwith "match_p"

let subst_tm x m n = unbindn_tm 0 [n] (bindn_tm 0 [x] m)
let substp_tm p m n =
  let xs = xs_of_p p in
  let ns = match_p p n in
  unbindn_tm 0 ns (bindn_tm 0 xs m)

(* miscellaneous *)

let lam rel s x a_opt m = Lam (rel, s, bind_ann x a_opt m)
let mLam r s args m =
  List.fold_right (fun (x, a_opt) -> lam r s x a_opt) args m

let rec fold_tl f acc tl =
  match tl with
  | TBase b -> (acc, b)
  | TBind (r, a, abs) ->
    let x, tl = unbind_tl abs in
    let acc, tl = f acc r a x tl in
    fold_tl f acc tl

let rec mkApps hd ms =
  match ms with
  | m :: ms -> mkApps (App (hd, m)) ms
  | [] -> hd

let unApps m =
  let rec aux m ns =
    match m with
    | App (m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []
