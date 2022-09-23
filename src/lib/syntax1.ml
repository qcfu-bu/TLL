open Names

type srt =
  | U
  | L
[@@deriving show { with_path = false }]

type rel =
  | N
  | R
[@@deriving show { with_path = false }]

type ('a, 'b) abs = Abs of 'a * 'b [@@deriving show { with_path = false }]

and tm =
  (* inference *)
  | Ann of tm * tm
  | Meta of M.t * tms
  (* core *)
  | Type of srt
  | Var of V.t
  | Pi of rel * srt * tm * (V.t, tm) abs
  | Lam of (V.t, tm) abs
  | App of tm * tm
  | Let of rel * tm * (V.t, tm) abs
  (* inductive *)
  | Data of D.t * tms
  | Cons of C.t * tms
  | Match of tm * mot * cls
  | Fix of (V.t, tm) abs

and tms = tm list
and tm_opt = tm option

and mot =
  | Mot0
  | Mot1 of (V.t, tm) abs
  | Mot2 of (p, tm) abs
  | Mot3 of (V.t, (p, tm) abs) abs

and p =
  | PVar of V.t
  | PData of D.t * V.t list
  | PCons of C.t * V.t list

and ps = p list
and cl = (p, tm) abs
and cls = cl list

type dcl =
  | DTm of rel * V.t * tm_opt * tm
  | DData of D.t * ptl * dconss
  | DAtom of rel * V.t * tm
[@@deriving show { with_path = false }]

and dcls = dcl list
and dcons = DCons of C.t * ptl
and dconss = dcons list

and ptl =
  | PBase of tl
  | PBind of tm * (V.t, ptl) abs

and tl =
  | TBase of tm
  | TBind of rel * tm * (V.t, tl) abs

let var x = Var x

let freshen_p = function
  | PVar x -> PVar (V.freshen x)
  | PData (d, xs) -> PData (d, List.map V.freshen xs)
  | PCons (c, xs) -> PCons (c, List.map V.freshen xs)

let xs_of_p = function
  | PVar x -> [ x ]
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
    | Ann (a, m) ->
      let a = aux k a in
      let m = aux k m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    | Type s -> Type s
    | Var y -> (
      let opt = findi_opt (fun _ x -> V.equal x y) xs in
      match opt with
      | Some (i, _) -> Var (V.bind (i + k))
      | None -> Var y)
    | Pi (r, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (r, s, a, Abs (x, b))
    | Lam (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (Abs (x, m))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (r, m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (r, m, Abs (x, n))
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
    | Fix (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Fix (Abs (x, m))
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
    | Ann (a, m) ->
      let a = aux k a in
      let m = aux k m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    | Type s -> Type s
    | Var y -> (
      match V.is_bound y sz k with
      | Some i -> List.nth xs (i - k)
      | None -> Var y)
    | Pi (r, s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (r, s, a, Abs (x, b))
    | Lam (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (Abs (x, m))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (r, m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (r, m, Abs (x, n))
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
    | Fix (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Fix (Abs (x, m))
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

let bindn_ptm k xs (Abs (p, m)) =
  let k = k + List.length (xs_of_p p) in
  let m = bindn_tm k xs m in
  Abs (p, m)

let rec unbindn_ptl k xs ptl =
  let rec aux k ptl =
    match ptl with
    | PBase tl -> PBase (unbindn_tl k xs tl)
    | PBind (a, Abs (x, ptl)) ->
      let a = unbindn_tm k xs a in
      let ptl = aux (k + 1) ptl in
      PBind (a, Abs (x, ptl))
  in
  aux k ptl

and unbindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase a -> TBase (unbindn_tm k xs a)
    | TBind (r, a, Abs (x, tl)) ->
      let a = unbindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (r, a, Abs (x, tl))
  in
  aux k tl

let unbindn_ptm k xs (Abs (p, m)) =
  let k = k + List.length (xs_of_p p) in
  let m = unbindn_tm k xs m in
  Abs (p, m)

let bind_tm x m = Abs (x, bindn_tm 0 [ x ] m)

let bindp_tm p m =
  let xs = xs_of_p p in
  Abs (p, bindn_tm 0 xs m)

let bind_ptl x ptl = Abs (x, bindn_ptl 0 [ x ] ptl)
let bind_tl x tl = Abs (x, bindn_tl 0 [ x ] tl)
let bind_ptm x ptm = Abs (x, bindn_ptm 0 [ x ] ptm)

let unbind_tm (Abs (x, m)) =
  let x = V.freshen x in
  (x, unbindn_tm 0 [ Var x ] m)

let unbindp_tm (Abs (p, m)) =
  let ps = freshen_p p in
  let xs = p |> xs_of_p |> List.map var in
  (ps, unbindn_tm 0 xs m)

let unbind_ptl (Abs (x, ptl)) =
  let x = V.freshen x in
  (x, unbindn_ptl 0 [ Var x ] ptl)

let unbind_tl (Abs (x, tl)) =
  let x = V.freshen x in
  (x, unbindn_tl 0 [ Var x ] tl)

let unbind_ptm (Abs (x, ptm)) =
  let x = V.freshen x in
  (x, unbindn_ptm 0 [ Var x ] ptm)

let unbind2_tm (Abs (x, m)) (Abs (_, n)) =
  let x = V.freshen x in
  let m = unbindn_tm 0 [ Var x ] m in
  let n = unbindn_tm 0 [ Var x ] n in
  (x, m, n)

let equal_p p1 p2 =
  match (p1, p2) with
  | PVar _, PVar _ -> true
  | PData (d1, xs1), PData (d2, xs2) ->
    D.equal d1 d2 && List.equal V.equal xs1 xs2
  | PCons (c1, xs1), PCons (c2, xs2) ->
    C.equal c1 c2 && List.equal V.equal xs1 xs2
  | _ -> false

let unbindp2_tm (Abs (p1, m)) (Abs (p2, n)) =
  if equal_p p1 p2 then
    let p = freshen_p p1 in
    let xs = p |> xs_of_p |> List.map var in
    let m = unbindn_tm 0 xs m in
    let n = unbindn_tm 0 xs n in
    (p, m, n)
  else
    failwith "unbindp2"

let unbind2_ptm (Abs (x, ptm1)) (Abs (_, ptm2)) =
  let x = V.freshen x in
  let ptm1 = unbindn_ptm 0 [ Var x ] ptm1 in
  let ptm2 = unbindn_ptm 0 [ Var x ] ptm2 in
  (x, ptm1, ptm2)

let equal_abs eq (Abs (_, m)) (Abs (_, n)) = eq m n
let equal_pabs eq (Abs (p1, m)) (Abs (p2, n)) = equal_p p1 p2 && eq m n
let asubst_tm (Abs (_, m)) n = unbindn_tm 0 [ n ] m
let asubst_tl (Abs (_, tl)) n = unbindn_tl 0 [ n ] tl
let asubst_ptl (Abs (_, ptl)) n = unbindn_ptl 0 [ n ] ptl

let match_p p m =
  match (p, m) with
  | PVar _, _ -> [ m ]
  | PData (d1, xs), Data (d2, ms) ->
    let xs_sz = List.length xs in
    let ms_sz = List.length ms in
    if D.equal d1 d2 && xs_sz = ms_sz then
      ms
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

let substp_tm p m n =
  let ns = match_p p n in
  let xs = xs_of_p p in
  unbindn_tm 0 ns (bindn_tm 0 xs m)

let subst_tm x m n = unbindn_tm 0 [ n ] (bindn_tm 0 [ x ] m)
let lam x m = Lam (bind_tm x m)
let mLam xs m = List.fold_right lam xs m

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

let rec occurs_tm x = function
  | Ann (a, m) -> occurs_tm x a || occurs_tm x m
  | Meta _ -> false
  | Type _ -> false
  | Var y -> V.equal x y
  | Pi (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs_tm x a || occurs_tm x b
  | Lam abs ->
    let _, m = unbind_tm abs in
    occurs_tm x m
  | App (m, n) -> occurs_tm x m || occurs_tm x n
  | Let (_, m, abs) ->
    let _, n = unbind_tm abs in
    occurs_tm x m || occurs_tm x n
  | Data (_, ms) -> List.exists (occurs_tm x) ms
  | Cons (_, ms) -> List.exists (occurs_tm x) ms
  | Match (m, mot, cls) ->
    let m_res = occurs_tm x m in
    let mot_res = occurs_mot x mot in
    let cls_res =
      List.exists
        (fun abs ->
          let _, m = unbindp_tm abs in
          occurs_tm x m)
        cls
    in
    m_res || mot_res || cls_res
  | Fix abs ->
    let _, m = unbind_tm abs in
    occurs_tm x m

and occurs_mot x = function
  | Mot0 -> false
  | Mot1 abs ->
    let _, a = unbind_tm abs in
    occurs_tm x a
  | Mot2 abs ->
    let _, a = unbindp_tm abs in
    occurs_tm x a
  | Mot3 ptm ->
    let _, abs = unbind_ptm ptm in
    let _, a = unbindp_tm abs in
    occurs_tm x a

let occurs_cls x cls =
  List.fold_left
    (fun acc pabs ->
      let _, m = unbindp_tm pabs in
      acc || occurs_tm x m)
    false cls

let rec occurs_tl x = function
  | TBase b -> occurs_tm x b
  | TBind (_, a, abs) ->
    if occurs_tm x a then
      true
    else
      let _, tl = unbind_tl abs in
      occurs_tl x tl
