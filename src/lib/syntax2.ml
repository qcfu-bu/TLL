open Names

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type ('a, 'b) abs = Abs of 'a * 'b [@@deriving show { with_path = false }]

and tm =
  | Var of V.t
  | Lam of sort * (V.t, tm) abs
  | App of sort * tm * tm
  | Let of tm * (V.t, tm) abs
  | Cons of C.t * tms
  | Match of sort * tm * cls
  | Fix of (V.t, tm) abs
  | Box

and tms = tm list

and p =
  | PVar of V.t
  | PCons of C.t * V.t list

and cl = (p, tm) abs
and cls = cl list

type dcl =
  | DTm of V.t * tm
  | DData of D.t * dconss
  | DAtom of V.t
[@@deriving show { with_path = false }]

and dcls = dcl list
and dcons = DCons of C.t * int
and dconss = dcons list

let var x = Var x

let freshen_p = function
  | PVar x -> PVar (V.freshen x)
  | PCons (c, xs) -> PCons (c, List.map V.freshen xs)

let xs_of_p = function
  | PVar x -> [ x ]
  | PCons (_, xs) -> xs

let findi_opt f ls =
  let rec aux k ls =
    match ls with
    | [] -> None
    | h :: t ->
      if f k h then
        Some (k, h)
      else
        aux (k + 1) t
  in
  aux 0 ls

let bindn_tm k xs m =
  let rec aux k m =
    match m with
    | Var y -> (
      let opt = findi_opt (fun _ x -> V.equal x y) xs in
      match opt with
      | Some (i, _) -> Var (V.bind (i + k))
      | None -> Var y)
    | Lam (s, Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (s, Abs (x, m))
    | App (s, m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (s, m, n)
    | Let (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (m, Abs (x, n))
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Match (s, m, cls) ->
      let m = aux k m in
      let cls =
        List.map
          (fun (Abs (p, m)) ->
            let xs = xs_of_p p in
            let k = k + List.length xs in
            let m = aux k m in
            Abs (p, m))
          cls
      in
      Match (s, m, cls)
    | Fix (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Fix (Abs (x, m))
    | Box -> Box
  in
  aux k m

let unbindn_tm k xs m =
  let sz = List.length xs in
  let rec aux k m =
    match m with
    | Var y -> (
      match V.is_bound y sz k with
      | Some i -> List.nth xs (i - k)
      | None -> Var y)
    | Lam (s, Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (s, Abs (x, m))
    | App (s, m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (s, m, n)
    | Let (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (m, Abs (x, n))
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Match (s, m, cls) ->
      let m = aux k m in
      let cls =
        List.map
          (fun (Abs (p, m)) ->
            let xs = xs_of_p p in
            let k = k + List.length xs in
            let m = aux k m in
            Abs (p, m))
          cls
      in
      Match (s, m, cls)
    | Fix (Abs (x, m)) ->
      let m = aux (k + 1) m in
      Fix (Abs (x, m))
    | Box -> Box
  in
  aux k m

let bindn_cls k xs cls =
  List.map
    (fun (Abs (p, rhs)) ->
      let k = k + List.length (xs_of_p p) in
      let rhs = bindn_tm k xs rhs in
      Abs (p, rhs))
    cls

let unbindn_cls k xs cls =
  List.map
    (fun (Abs (p, rhs)) ->
      let k = k + List.length (xs_of_p p) in
      let rhs = unbindn_tm k xs rhs in
      Abs (p, rhs))
    cls

let bind_tm x m = Abs (x, bindn_tm 0 [ x ] m)
let bind_tm_abs f x m = Abs (f, Abs (x, bindn_tm 0 [ f; x ] m))

let bindp_tm p m =
  let xs = xs_of_p p in
  Abs (p, bindn_tm 0 xs m)

let unbind_tm (Abs (x, m)) =
  let x = V.freshen x in
  (x, unbindn_tm 0 [ Var x ] m)

let unbind_tm_abs (Abs (f, Abs (x, m))) =
  let f = V.freshen f in
  let x = V.freshen x in
  (f, x, unbindn_tm 0 [ Var f; Var x ] m)

let unbindp_tm (Abs (p, rhs)) =
  let p = freshen_p p in
  let xs = p |> xs_of_p |> List.map var in
  (p, unbindn_tm 0 xs rhs)

let equal_p p1 p2 =
  match (p1, p2) with
  | PVar _, PVar _ -> true
  | PCons (c1, xs1), PCons (c2, xs2) ->
    C.equal c1 c2 && List.equal V.equal xs1 xs2
  | _ -> false

let match_p p m =
  match (p, m) with
  | PVar _, _ -> [ m ]
  | PCons (c1, xs), Cons (c2, ms) ->
    let xs_sz = List.length xs in
    let ms_sz = List.length ms in
    if C.equal c1 c2 && xs_sz = ms_sz then
      ms
    else
      failwith "match_p"
  | _ -> failwith "match_p"

let asubst_tm (Abs (_, m)) n = unbindn_tm 0 [ n ] m
let asubstp_tm (Abs (p, m)) n = unbindn_tm 0 (match_p p n) m
let subst_tm x m n = unbindn_tm 0 [ n ] (bindn_tm 0 [ x ] m)

let rec mkApps s hd ms =
  match ms with
  | m :: ms -> mkApps s (App (s, hd, m)) ms
  | [] -> hd

let unApps m =
  let rec aux m ns =
    match m with
    | App (_, m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []

let equal_abs eq (Abs (_, m)) (Abs (_, n)) = eq m n

let rec occurs_tm x m =
  match m with
  | Var y -> V.equal x y
  | Lam (_, abs) ->
    let _, m = unbind_tm abs in
    occurs_tm x m
  | App (_, m, n) -> occurs_tm x m || occurs_tm x n
  | Let (m, abs) ->
    let _, n = unbind_tm abs in
    occurs_tm x m || occurs_tm x n
  | Cons (_, ms) -> List.exists (occurs_tm x) ms
  | Match (_, m, cls) ->
    let m_res = occurs_tm x m in
    let cls_res =
      List.exists
        (fun pabs ->
          let _, rhs = unbindp_tm pabs in
          occurs_tm x rhs)
        cls
    in
    m_res || cls_res
  | Fix abs ->
    let _, m = unbind_tm abs in
    occurs_tm x m
  | Box -> false
