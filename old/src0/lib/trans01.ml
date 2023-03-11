open Fmt
open Names
open Syntax0

type entry =
  | V of V.t
  | D of D.t
  | C of C.t

type nspc = (string * entry) list

let find_v s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | V _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, V x) -> Some x
  | _ -> None

let find_c s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | C _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, C c) -> Some c
  | _ -> None

let find_d s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | D _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, D d) -> Some d
  | _ -> None

let trans_rel r =
  match r with
  | R -> Syntax1.R
  | N -> Syntax1.N

let trans_sort s =
  match s with
  | U -> Syntax1.U
  | L -> Syntax1.L

let spine_of_nspc nspc =
  List.fold_left
    (fun acc (_, entry) ->
      match entry with
      | V x -> Syntax1.Var x :: acc
      | D _ -> acc
      | C _ -> acc)
    [] nspc

let rec trans_p nspc p =
  match p with
  | PVar id ->
    let x = V.mk id in
    ((id, V x) :: nspc, Syntax1.PVar x)
  | PCons (id, xs) -> (
    match find_c id nspc with
    | Some c ->
      let nspc, xs = trans_xs nspc xs in
      (nspc, Syntax1.PCons (c, xs))
    | _ -> failwith "trans_p")
  | PData (id, xs) -> (
    match find_d id nspc with
    | Some d ->
      let nspc, xs = trans_xs nspc xs in
      (nspc, Syntax1.PData (d, xs))
    | _ -> failwith "trans_p")

and trans_xs nspc ids =
  match ids with
  | [] -> (nspc, [])
  | id :: ids ->
    let x = V.mk id in
    let nspc, xs = trans_xs ((id, V x) :: nspc) ids in
    (nspc, x :: xs)

let rec trans_tm nspc m =
  match m with
  | Ann (a, m) ->
    let a = trans_tm nspc a in
    let m = trans_tm nspc m in
    Syntax1.Ann (a, m)
  | Type s -> Syntax1.Type (trans_sort s)
  | Id "_" -> Syntax1.Meta (M.mk (), spine_of_nspc nspc)
  | Id id -> (
    match List.assoc_opt id nspc with
    | Some (V x) -> Syntax1.Var x
    | Some (D d) -> Syntax1.Data (d, [])
    | Some (C c) -> Syntax1.Cons (c, [])
    | _ -> failwith "trans_Id(%s)" id)
  | Pi (r, s, id, a, b) ->
    let a = trans_tm nspc a in
    let x = V.mk id in
    let nspc = (id, V x) :: nspc in
    let b = trans_tm nspc b in
    Syntax1.(Pi (trans_rel r, trans_sort s, a, bind_tm x b))
  | Lam (r, s, id, m) ->
    let x = V.mk id in
    let nspc = (id, V x) :: nspc in
    let m = trans_tm nspc m in
    Syntax1.(Lam (trans_rel r, trans_sort s, bind_tm x m))
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      let ms = List.map (trans_tm nspc) ms in
      match List.assoc_opt id nspc with
      | Some (V x) -> Syntax1.(mkApps (Var x) ms)
      | Some (D d) -> Syntax1.(Data (d, ms))
      | Some (C c) -> Syntax1.(Cons (c, ms))
      | None -> failwith "trans_App(%a)" pp_tm m)
    | m :: ms ->
      let m = trans_tm nspc m in
      let ms = List.map (trans_tm nspc) ms in
      Syntax1.mkApps m ms
    | _ -> failwith "trans_App(%a)" pp_tm m)
  | Let (r, id, m, n) ->
    let m = trans_tm nspc m in
    let x = V.mk id in
    let nspc = (id, V x) :: nspc in
    let n = trans_tm nspc n in
    Syntax1.(Let (trans_rel r, m, bind_tm x n))
  | Match (m, mot, cls) ->
    let m = trans_tm nspc m in
    let mot = trans_mot nspc mot in
    let cls = trans_cls nspc cls in
    Syntax1.(Match (m, mot, cls))
  | Fix (id, m) ->
    let x = V.mk id in
    let m = trans_tm ((id, V x) :: nspc) m in
    Syntax1.(Fix (bind_tm x m))

and trans_mot nspc mot =
  match mot with
  | Mot0 -> Syntax1.Mot0
  | Mot1 (id, m) ->
    let x = V.mk id in
    let m = trans_tm ((id, V x) :: nspc) m in
    Syntax1.(Mot1 (bind_tm x m))
  | Mot2 (p, m) ->
    let nspc, p = trans_p nspc p in
    let m = trans_tm nspc m in
    Syntax1.(Mot2 (bindp_tm p m))
  | Mot3 (id, p, m) ->
    let x = V.mk id in
    let nspc, p = trans_p ((id, V x) :: nspc) p in
    let m = trans_tm nspc m in
    Syntax1.(Mot3 (bind_ptm x (bindp_tm p m)))

and trans_cl nspc (p, rhs) =
  let nspc, p = trans_p nspc p in
  let rhs = trans_tm nspc rhs in
  Syntax1.(bindp_tm p rhs)

and trans_cls nspc cls = List.map (trans_cl nspc) cls

let rec trans_ptl nspc ptl =
  match ptl with
  | PBase tl -> Syntax1.(PBase (trans_tl nspc tl))
  | PBind (id, a, b) ->
    let a = trans_tm nspc a in
    let x = V.mk id in
    let b = trans_ptl ((id, V x) :: nspc) b in
    Syntax1.(PBind (a, bind_ptl x b))

and trans_tl nspc tl =
  match tl with
  | TBase a -> Syntax1.(TBase (trans_tm nspc a))
  | TBind (r, id, a, b) ->
    let a = trans_tm nspc a in
    let x = V.mk id in
    let b = trans_tl ((id, V x) :: nspc) b in
    Syntax1.(TBind (trans_rel r, a, bind_tl x b))

let trans_dcons nspc (DCons (id, ptl)) =
  let c = C.mk id in
  let ptl = trans_ptl nspc ptl in
  let nspc = (id, C c) :: nspc in
  (nspc, Syntax1.(DCons (c, ptl)))

let rec trans_dconss nspc dconss =
  match dconss with
  | [] -> (nspc, [])
  | dcons :: dconss ->
    let nspc, dcons = trans_dcons nspc dcons in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, dcons :: dconss)

let trans_dcl nspc dcl =
  match dcl with
  | DTm (r, id, args, b_opt, m) ->
    let x = V.mk id in
    let f = V.mk id in
    let args, nspc =
      List.fold_left
        (fun (args, nspc) (r, id, a) ->
          let x = V.mk id in
          let a = trans_tm nspc a in
          let nspc = (id, V x) :: nspc in
          ((trans_rel r, x, a) :: args, nspc))
        ([], nspc) args
    in
    let b =
      match b_opt with
      | Some b -> trans_tm nspc b
      | None -> Syntax1.Meta (M.mk (), spine_of_nspc nspc)
    in
    let a, m =
      List.fold_left
        (fun (b, m) (r, x, a) ->
          Syntax1.(Pi (r, U, a, bind_tm x b), Lam (r, U, bind_tm x m)))
        (b, trans_tm ((id, V f) :: nspc) m)
        args
    in
    let nspc = (id, V x) :: nspc in
    if Syntax1.occurs_tm f m then
      let m = Syntax1.(Fix (bind_tm f m)) in
      (nspc, Syntax1.(DTm (trans_rel r, x, Some a, m)))
    else
      (nspc, Syntax1.(DTm (trans_rel r, x, Some a, m)))
  | DData (id, ptl, dconss) ->
    let d = D.mk id in
    let ptl = trans_ptl nspc ptl in
    let nspc = (id, D d) :: nspc in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, Syntax1.DData (d, ptl, dconss))
  | DAtom (r, id, a) ->
    let a = trans_tm nspc a in
    let x = V.mk id in
    let nspc = (id, V x) :: nspc in
    (nspc, Syntax1.(DAtom (trans_rel r, x, a)))

let rec trans_dcls nspc dcls =
  match dcls with
  | [] -> (nspc, [])
  | dcl :: dcls ->
    let nspc, dcl = trans_dcl nspc dcl in
    let nspc, dcls = trans_dcls nspc dcls in
    (nspc, dcl :: dcls)
