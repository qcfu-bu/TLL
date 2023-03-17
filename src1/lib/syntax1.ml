open Fmt
open Names

(* syntax definitions *)

type sort = U | L
[@@deriving show { with_path = false }]

type rel = N | R
[@@deriving show { with_path = false }]

type ('a, 'b) abs = Abs of 'a * 'b
[@@deriving show { with_path = false }]

type ('a, 'b) abs_opt = ('a, 'b) abs option
[@@deriving show { with_path = false }]

type role = Pos | Neg
[@@deriving show { with_path = false }]

type prim = Stdin | Stdout | Stderr
[@@deriving show { with_path = false }]

type tm =
  (* inference *)
  | Ann of tm * tm
  | Meta of M.t * tms
  (* core *)
  | Type of sort
  | Var of V.t
  | Pi of rel * sort * tm * (V.t, tm) abs
  | Lam of rel * sort * (V.t * tm_opt, tm) abs
  | App of tm * tm
  | Let of rel * tm * (V.t * tm_opt, tm) abs
  (* data *)
  | Sig of rel * sort * tm * (V.t, tm) abs
  | Pair of rel * sort * tm * tm
  | Data of D.t * tms
  | Cons of C.t *  tms
  | Match of tm * (V.t, tm) abs_opt * cls
  (* equality *)
  | Eq of tm * tm
  | Refl
  | Rew of (V.t * V.t, tm) abs * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | Do of tm * (V.t * tm_opt, tm) abs
  (* session *)
  | Proto
  | End of role
  | Act of rel * role * tm * (V.t, tm) abs
  | Ch of role * tm
  | Open of prim
  | Fork of tm * (V.t, tm) abs
  | Recv of rel * tm
  | Send of rel * tm
  | Close of tm

and tms = tm list
and tm_opt = tm option
and tms_opt = tms option

and p =
  | PVar of V.t
  | PPair of rel * sort * V.t * V.t
  | PCons of C.t * V.t list

and ps = p list
and cl = (p, tm) abs
and cls = cl list
[@@deriving show { with_path = false }]

type dcl =
  | DTm of rel * V.t * tm_opt * tm
  | DData of D.t * tm param * dconss

and dcls = dcl list
and dcons = DCons of C.t * tele param
and dconss = dcons list

and 'a param =
  | PBase of 'a
  | PBind of tm * (V.t, 'a param) abs

and tele =
  | TBase of tm
  | TBind of rel * tm * (V.t, tele) abs
[@@deriving show { with_path = false }]

(* utility *)

let var x = Var x

let freshen_p = function
  | PVar x -> PVar (V.freshen x)
  | PPair (rel, s, x, y) -> PPair (rel, s, V.freshen x, V.freshen y)
  | PCons (c, xs) -> PCons (c, List.map V.freshen xs)

let xs_of_p = function
  | PVar x -> [ x ]
  | PPair (_, _, x, y) -> [x; y]
  | PCons (_, xs) -> xs

let equal_p p1 p2 =
  match p1, p2 with
  | PVar _, PVar _ -> true
  | PPair (rel1, s1, _, _), PPair (rel2, s2, _, _) ->
    rel1 = rel2 && s1 = s2 
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
      let mot =
        Option.map
          (fun (Abs (x, m)) ->
             Abs (x, aux (k + 1) m)) mot
      in
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
    | Refl -> Refl
    | Rew (Abs ((x, y), c), pf, m) ->
      let c = aux (k + 2) c in
      let pf = aux k pf in
      let m = aux k m in
      Rew (Abs ((x, y), c), pf, m)
    (* monadic *)
    | IO a -> IO (aux k a)
    | Return m -> Return (aux k m)
    | Do (m, Abs ((x, a_opt), n)) ->
      let m = aux k m in
      let a_opt = Option.map (aux k) a_opt in
      let n = aux (k + 1) n in
      Do (m, Abs ((x, a_opt), n))
    (* session *)
    | Proto -> Proto
    | End rol -> End rol
    | Act (rel, rol, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (rel, rol, a, Abs (x, b))
    | Ch (rol, a) -> Ch (rol, aux k a)
    | Open prim -> Open prim
    | Fork (a, Abs (x, m)) ->
      let a = aux k a in
      let m = aux (k + 1) m in
      Fork (a, Abs (x, m))
    | Recv (rel, m) -> Recv (rel, aux k m)
    | Send (rel, m) -> Send (rel, aux k m)
    | Close m -> Close (aux k m)
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
      let mot =
        Option.map
          (fun (Abs (x, m)) ->
             Abs (x, aux (k + 1) m)) mot
      in
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
    | Refl -> Refl
    | Rew (Abs ((x, y), c), pf, m) ->
      let c = aux (k + 2) c in
      let pf = aux k pf in
      let m = aux k m in
      Rew (Abs ((x, y), c), pf, m)
    (* monadic *)
    | IO a -> IO (aux k a)
    | Return m -> Return (aux k m)
    | Do (m, Abs ((x, a_opt), n)) ->
      let m = aux k m in
      let a_opt = Option.map (aux k) a_opt in
      let n = aux (k + 1) n in
      Do (m, Abs ((x, a_opt), n))
    (* session *)
    | Proto -> Proto
    | End rol -> End rol
    | Act (rel, rol, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (rel, rol, a, Abs (x, b))
    | Ch (rol, a) -> Ch (rol, aux k a)
    | Open prim -> Open prim
    | Fork (a, Abs (x, m)) ->
      let a = aux k a in
      let m = aux (k + 1) m in
      Fork (a, Abs (x, m))
    | Recv (rel, m) -> Recv (rel, aux k m)
    | Send (rel, m) -> Send (rel, aux k m)
    | Close m -> Close (aux k m)
  in
  aux k m

let rec bindn_param f k xs param =
  let rec aux k param =
    match param with
    | PBase b -> PBase (f k xs b)
    | PBind (a, Abs (x, param)) ->
      let a = bindn_tm k xs a in
      let param = aux (k + 1) param in
      PBind (a, Abs (x, param))
  in
  aux k param

and bindn_tele k xs tele =
  let rec aux k tele =
    match tele with
    | TBase b -> TBase (bindn_tm k xs b)
    | TBind (r, a, Abs (x, tele)) ->
      let a = bindn_tm k xs a in
      let tele = aux (k + 1) tele in
      TBind (r, a, Abs (x, tele))
  in
  aux k tele

let rec unbindn_param f k xs param =
  let rec aux k param =
    match param with
    | PBase b -> PBase (f k xs b)
    | PBind (a, Abs (x, param)) ->
      let a = unbindn_tm k xs a in
      let param = aux (k + 1) param in
      PBind (a, Abs (x, param))
  in
  aux k param

and unbindn_tele k xs tele =
  let rec aux k tele =
    match tele with
    | TBase a -> TBase (unbindn_tm k xs a)
    | TBind (r, a, Abs (x, tele)) ->
      let a = unbindn_tm k xs a in
      let tele = aux (k + 1) tele in
      TBind (r, a, Abs (x, tele))
  in
  aux k tele

let bind_tm x m = Abs (x, bindn_tm 0 [x] m)
let bind_ann x a_opt m = Abs ((x, a_opt), bindn_tm 0 [x] m)
let bind_tm2 x y m = Abs ((x, y), bindn_tm 0 [x; y] m)
let bindp_tm p m =
  let xs = xs_of_p p in
  Abs (p, bindn_tm 0 xs m)
let bind_param f x param = Abs (x, bindn_param f 0 [x] param)
let bind_tele x tele = Abs (x, bindn_tele 0 [x] tele)

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
let unbind_param f (Abs (x, param)) =
  let x = V.freshen x in
  (x, unbindn_param f 0 [Var x] param)
let unbind_tele (Abs (x, tele)) =
  let x = V.freshen x in
  (x, unbindn_tele 0 [Var x] tele)

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
let unbind2_tm2 (Abs ((x, y), m)) (Abs ((_, _), n)) =
  let x = V.freshen x in
  let y = V.freshen y in
  let m = unbindn_tm 0 [Var x; Var y] m in
  let n = unbindn_tm 0 [Var x; Var y] n in
  ((x, y), m, n)
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
let asubst_tele (Abs (_, tele)) n = unbindn_tele 0 [n] tele
let asubst_param f (Abs (_, param)) n = unbindn_param f 0 [n] param

let match_p p m =
  match p, m with
  | PVar _, _ -> [m]
  | PPair (rel1, s1, _, _), Pair (rel2, s2, m, n) ->
    if rel1 = rel2 && s1 = s2 then
      [m; n]
    else
      failwith "match_p"
  | PCons (c1, xs), Cons (c2, ms) ->
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

let rec fold_tl f acc tele =
  match tele with
  | TBase b -> (acc, b)
  | TBind (r, a, abs) ->
    let x, tele = unbind_tele abs in
    let acc, tele = f acc r a x tele in
    fold_tl f acc tele

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
