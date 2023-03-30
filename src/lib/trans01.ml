open Fmt
open Util
open Bindlib
open Names
open Syntax0

type entry =
  | V of Syntax1.V.t
  | F of Syntax1.V.t
  | D of D.t
  | C of C.t * int

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
  | Some (_, C (c, i)) -> Some (c, i)
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

let trans_sort = function
  | U -> Syntax1.U
  | L -> Syntax1.L

let trans_rel = function
  | R -> Syntax1.R
  | N -> Syntax1.N

let trans_role = function
  | Pos -> Syntax1.Pos
  | Neg -> Syntax1.Neg

let trans_prim = function
  | Stdin -> Syntax1.Stdin
  | Stdout -> Syntax1.Stdout
  | Stderr -> Syntax1.Stderr

let spine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | V x -> Syntax1._Var x :: acc
      | F x -> acc
      | D _ -> acc
      | C _ -> acc)
    nspc []

let mk_meta nspc = Syntax1.(_Meta (M.mk ()) (box_list (spine_of_nspc nspc)))

let mk_param nspc i =
  let rec loop i =
    if i <= 0 then
      []
    else
      mk_meta nspc :: loop (i - 1)
  in
  box_list (loop i)

let rec trans_xs nspc = function
  | [] -> (nspc, [])
  | id :: ids ->
    let x = Syntax1.mk id in
    let nspc, xs = trans_xs ((id, V x) :: nspc) ids in
    (nspc, x :: xs)

let rec trans_tm nspc = function
  (* inference *)
  | Ann (m, a) ->
    let m = trans_tm nspc m in
    let a = trans_tm nspc a in
    Syntax1._Ann m a
  (* core *)
  | Type s -> Syntax1.(_Type (trans_sort s))
  | Id "_" -> mk_meta nspc
  | Id id -> (
    match List.assoc_opt id nspc with
    | Some (V x) -> Syntax1._Var x
    | Some (F x) -> Syntax1._Var x
    | Some (D d) -> Syntax1._Data d (box [])
    | Some (C (c, i)) -> Syntax1._Cons c (mk_param nspc i) (box [])
    | None -> failwith "trans_tm Id")
  | Pi (rel, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.mk id in
    let b = trans_tm ((id, V x) :: nspc) b in
    Syntax1.(_Pi (trans_rel rel) (trans_sort s) a (bind_var x b))
  | Lam (rel, s, Binder (id, m)) ->
    let x = Syntax1.mk id in
    let m = trans_tm ((id, V x) :: nspc) m in
    Syntax1.(_Lam (trans_rel rel) (trans_sort s) (bind_var x m))
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      let ms = List.map (trans_tm nspc) ms in
      match List.assoc_opt id nspc with
      | Some (V x) -> Syntax1.(_mkApps (_Var x) ms)
      | Some (F x) -> Syntax1.(_mkApps (_Var x) ms)
      | Some (D d) -> Syntax1.(_Data d (box_list ms))
      | Some (C (c, i)) -> Syntax1.(_Cons c (mk_param nspc i) (box_list ms))
      | None -> failwith "trans_tm App(%s)" id)
    | m :: ms ->
      let m = trans_tm nspc m in
      let ms = List.map (trans_tm nspc) ms in
      Syntax1._mkApps m ms
    | _ -> failwith "trans_tm App")
  | Let (rel, m, Binder (opt, n)) -> (
    match opt with
    | Left id ->
      let m = trans_tm nspc m in
      let x = Syntax1.mk id in
      let n = trans_tm ((id, V x) :: nspc) n in
      Syntax1.(_Let (trans_rel rel) m (bind_var x n))
    | Right p ->
      let m = trans_tm nspc m in
      let x = Syntax1.mk "_" in
      let cls = box_list [ trans_cl nspc (Binder (p, n)) ] in
      let mot = bind_var x (mk_meta nspc) in
      let n = Syntax1.(_Match (_Var x) mot cls) in
      Syntax1.(_Let (trans_rel rel) m (bind_var x n)))
  | Fix (id1, Binder (id2, m)) -> (
    match List.assoc_opt id1 nspc with
    | Some (V x) ->
      let r = Syntax1.mk id2 in
      let m = trans_tm ((id2, V r) :: nspc) m in
      Syntax1.(_Fix x (bind_var r m))
    | _ -> failwith "trans_tm Fix")
  (* data *)
  | Sigma (rel, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.mk id in
    let b = trans_tm ((id, V x) :: nspc) b in
    Syntax1.(_Sigma (trans_rel rel) (trans_sort s) a (bind_var x b))
  | Pair (rel, s, m, n) ->
    let m = trans_tm nspc m in
    let n = trans_tm nspc n in
    Syntax1.(_Pair (trans_rel rel) (trans_sort s) m n)
  | Match (m, Binder (id, a), cls) ->
    let m = trans_tm nspc m in
    let x = Syntax1.mk id in
    let a = trans_tm ((id, V x) :: nspc) a in
    let cls = List.map (trans_cl nspc) cls in
    Syntax1.(_Match m (bind_var x a) (box_list cls))
  (* equality *)
  | Eq (m, n) ->
    let m = trans_tm nspc m in
    let n = trans_tm nspc n in
    Syntax1.(_Eq (mk_meta nspc) m n)
  | Refl -> Syntax1.(_Refl (mk_meta nspc))
  | Rew (Binder ((id1, id2), a), pf, m) ->
    let pf = trans_tm nspc pf in
    let m = trans_tm nspc m in
    let nspc, xs = trans_xs nspc [ id1; id2 ] in
    let a = trans_tm nspc a in
    let bnd = bind_mvar (Array.of_list xs) a in
    Syntax1.(_Rew bnd pf m)
  (* monadic *)
  | IO a -> Syntax1.(_IO (trans_tm nspc a))
  | Return m -> Syntax1.(_Return (trans_tm nspc m))
  | MLet (m, Binder (opt, n)) -> (
    match opt with
    | Left id ->
      let m = trans_tm nspc m in
      let x = Syntax1.mk id in
      let n = trans_tm ((id, V x) :: nspc) n in
      Syntax1.(_MLet m (bind_var x n))
    | Right p ->
      let m = trans_tm nspc m in
      let x = Syntax1.mk "_" in
      let cls = box_list [ trans_cl nspc (Binder (p, n)) ] in
      let mot = bind_var x (mk_meta nspc) in
      let n = Syntax1.(_Match (_Var x) mot cls) in
      Syntax1.(_MLet m (bind_var x n)))
  (* session *)
  | Proto -> Syntax1._Proto
  | End -> Syntax1.(_End)
  | Act (rel, rol, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.mk id in
    let b = trans_tm ((id, V x) :: nspc) b in
    Syntax1.(_Act (trans_rel rel) (trans_role rol) a (bind_var x b))
  | Ch (rol, m) -> Syntax1.(_Ch (trans_role rol) (trans_tm nspc m))
  | Open prim -> Syntax1.(_Open (trans_prim prim))
  | Fork (a, Binder (id, m)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.mk id in
    let m = trans_tm ((id, V x) :: nspc) m in
    Syntax1.(_Fork a (bind_var x m))
  | Recv m -> Syntax1.(_Recv (trans_tm nspc m))
  | Send m -> Syntax1.(_Send (trans_tm nspc m))
  | Close m -> Syntax1.(_Close (trans_tm nspc m))

and trans_cl nspc = function
  | Binder (PPair (rel, s, id1, id2), m) ->
    let nspc, xs = trans_xs nspc [ id1; id2 ] in
    let m = trans_tm nspc m in
    let bnd = bind_mvar (Array.of_list xs) m in
    Syntax1.(_PPair (trans_rel rel) (trans_sort s) bnd)
  | Binder (PCons (id, ids), m) -> (
    match find_c id nspc with
    | Some (c, _) ->
      let nspc, xs = trans_xs nspc ids in
      let m = trans_tm nspc m in
      let bnd = bind_mvar (Array.of_list xs) m in
      Syntax1.(_PCons c bnd)
    | _ -> failwith "trans_tm Match")

let rec trans_param trans nspc = function
  | PBase a -> Syntax1.(_PBase (trans nspc a), 0)
  | PBind (a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.mk id in
    let b, i = trans_param trans ((id, V x) :: nspc) b in
    Syntax1.(_PBind a (bind_var x b), i + 1)

let rec trans_tele nspc = function
  | TBase a -> Syntax1.(_TBase (trans_tm nspc a))
  | TBind (rel, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.mk id in
    let b = trans_tele ((id, V x) :: nspc) b in
    Syntax1.(_TBind (trans_rel rel) a (bind_var x b))

let rec trans_args entry nspc = function
  | ABase (m, b) ->
    let b = trans_tm nspc b in
    let m = trans_tm (entry :: nspc) m in
    (m, b)
  | ABind (rel, a, Binder (id, args)) ->
    let x = Syntax1.mk id in
    let a = trans_tm nspc a in
    let m, b = trans_args entry ((id, V x) :: nspc) args in
    Syntax1.
      ( _Lam (trans_rel rel) U (bind_var x m)
      , _Pi (trans_rel rel) U a (bind_var x b) )

let trans_dcons nspc (DCons (id, ptl)) =
  let c = C.mk id in
  let ptl, i = trans_param trans_tele nspc ptl in
  ((id, C (c, i)) :: nspc, Syntax1.(_DCons c ptl))

let rec trans_dconss nspc = function
  | [] -> (nspc, [])
  | dcons :: dconss ->
    let nspc, dcons = trans_dcons nspc dcons in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, dcons :: dconss)

let rec trans_dcl nspc = function
  | DTm (rel, id, args) ->
    let x = Syntax1.mk id in
    let r = Syntax1.mk id in
    let m, a = trans_args (id, F r) nspc args in
    let nspc = (id, V x) :: nspc in
    if Bindlib.occur r m then
      let m = Syntax1.(_Fix x (bind_var r m)) in
      (nspc, Syntax1.(_DTm (trans_rel rel) x a m))
    else
      (nspc, Syntax1.(_DTm (trans_rel rel) x a m))
  | DData (id, ptm, dconss) ->
    let d = D.mk id in
    let ptm, _ = trans_param trans_tm nspc ptm in
    let nspc = (id, D d) :: nspc in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, Syntax1._DData d ptm (box_list dconss))

let trans_dcls nspc dcls =
  let rec aux nspc dcls =
    match dcls with
    | [] -> (nspc, [])
    | dcl :: dcls ->
      let nspc, dcl = trans_dcl nspc dcl in
      let nspc, dcls = aux nspc dcls in
      (nspc, dcl :: dcls)
  in
  let nspc, dcls = aux nspc dcls in
  (nspc, unbox (box_list dcls))
