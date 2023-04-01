open Fmt
open Util
open Bindlib
open Names
open Syntax0

type nspc_entry =
  | EVar of Syntax1.V.t
  | EConst of Syntax1.V.t * int
  | ESVar of Syntax1.SV.t
  | EData of D.t * int
  | ECons of C.t * int * int

type nspc = (string * nspc_entry) list

let find_var s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | EVar _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, EVar x) -> Some x
  | _ -> None

let find_const s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | EConst _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, EConst (x, _)) -> Some x
  | _ -> None

let find_svar s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | ESVar _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, ESVar x) -> Some x
  | _ -> None

let find_cons s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | ECons _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, ECons (c, i, j)) -> Some (c, i, j)
  | _ -> None

let find_data s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | EData _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, EData (d, i)) -> Some (d, i)
  | _ -> None

let trans_sort nspc = function
  | U -> Syntax1._U
  | L -> Syntax1._L
  | SId "_" -> Syntax1.(_SMeta (M.mk ()))
  | SId id -> (
    match find_svar id nspc with
    | Some sv -> Syntax1.(_SVar sv)
    | None -> failwith "trans_sort")

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
      | EVar x -> Syntax1._Var x :: acc
      | _ -> acc)
    nspc []

let mk_meta nspc = Syntax1.(_Meta (M.mk ()) (box_list (spine_of_nspc nspc)))

let mk_inst i =
  let rec loop i =
    if i <= 0 then
      []
    else
      Syntax1.(_SMeta (M.mk ())) :: loop (i - 1)
  in
  box_list (loop i)

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
    let x = Syntax1.(V.mk id) in
    let nspc, xs = trans_xs ((id, EVar x) :: nspc) ids in
    (nspc, x :: xs)

let rec trans_tm nspc = function
  (* inference *)
  | Ann (m, a) ->
    let m = trans_tm nspc m in
    let a = trans_tm nspc a in
    Syntax1._Ann m a
  (* core *)
  | Type s -> Syntax1.(_Type (trans_sort nspc s))
  | Id "_" -> mk_meta nspc
  | Id id -> (
    match List.assoc_opt id nspc with
    | Some (EVar x) -> Syntax1._Var x
    | Some (EConst (x, i)) -> Syntax1.(_Const x (mk_inst i))
    | Some (EData (d, i)) -> Syntax1._Data d (mk_inst i) (box [])
    | Some (ECons (c, i, j)) ->
      Syntax1._Cons c (mk_inst i) (mk_param nspc j) (box [])
    | _ -> failwith "trans_tm Id")
  | Inst (id, ss) -> (
    let ss = List.map (trans_sort nspc) ss in
    let ss = box_list ss in
    match List.assoc_opt id nspc with
    | Some (EConst (x, _)) -> Syntax1.(_Const x ss)
    | Some (EData (d, _)) -> Syntax1.(_Data d ss (box []))
    | Some (ECons (c, _, j)) -> Syntax1.(_Cons c ss (mk_param nspc j) (box []))
    | _ -> failwith "trans_tm Inst")
  | Pi (rel, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.(_Pi (trans_rel rel) (trans_sort nspc s) a (bind_var x b))
  | Lam (rel, s, Binder (id, m)) ->
    let x = Syntax1.(V.mk id) in
    let m = trans_tm ((id, EVar x) :: nspc) m in
    Syntax1.(_Lam (trans_rel rel) (trans_sort nspc s) (bind_var x m))
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      let ms = List.map (trans_tm nspc) ms in
      match List.assoc_opt id nspc with
      | Some (EVar x) -> Syntax1.(_mkApps (_Var x) ms)
      | Some (EConst (x, i)) -> Syntax1.(_mkApps (_Const x (mk_inst i)) ms)
      | Some (EData (d, i)) -> Syntax1.(_Data d (mk_inst i) (box_list ms))
      | Some (ECons (c, i, j)) ->
        Syntax1.(_Cons c (mk_inst i) (mk_param nspc j) (box_list ms))
      | _ -> failwith "trans_tm App(%s)" id)
    | Inst (id, ss) :: ms -> (
      let ss = List.map (trans_sort nspc) ss in
      let ms = List.map (trans_tm nspc) ms in
      match List.assoc_opt id nspc with
      | Some (EConst (x, _)) -> Syntax1.(_mkApps (_Const x (box_list ss)) ms)
      | Some (EData (d, _)) -> Syntax1.(_Data d (box_list ss) (box_list ms))
      | Some (ECons (c, _, j)) ->
        Syntax1.(_Cons c (box_list ss) (mk_param nspc j) (box_list ms))
      | _ -> failwith "trans_tm Inst")
    | m :: ms ->
      let m = trans_tm nspc m in
      let ms = List.map (trans_tm nspc) ms in
      Syntax1._mkApps m ms
    | _ -> failwith "trans_tm App")
  | Let (rel, m, Binder (opt, n)) -> (
    match opt with
    | Left id ->
      let m = trans_tm nspc m in
      let x = Syntax1.(V.mk id) in
      let n = trans_tm ((id, EVar x) :: nspc) n in
      Syntax1.(_Let (trans_rel rel) m (bind_var x n))
    | Right p ->
      let m = trans_tm nspc m in
      let x = Syntax1.(V.mk "_") in
      let cls = box_list [ trans_cl nspc (Binder (p, n)) ] in
      let mot = bind_var x (mk_meta nspc) in
      let n = Syntax1.(_Match (_Var x) mot cls) in
      Syntax1.(_Let (trans_rel rel) m (bind_var x n)))
  (* data *)
  | Sigma (rel, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.(_Sigma (trans_rel rel) (trans_sort nspc s) a (bind_var x b))
  | Pair (rel, s, m, n) ->
    let m = trans_tm nspc m in
    let n = trans_tm nspc n in
    Syntax1.(_Pair (trans_rel rel) (trans_sort nspc s) m n)
  | Match (m, Binder (id, a), cls) ->
    let m = trans_tm nspc m in
    let x = Syntax1.(V.mk id) in
    let a = trans_tm ((id, EVar x) :: nspc) a in
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
      let x = Syntax1.(V.mk id) in
      let n = trans_tm ((id, EVar x) :: nspc) n in
      Syntax1.(_MLet m (bind_var x n))
    | Right p ->
      let m = trans_tm nspc m in
      let x = Syntax1.(V.mk "_") in
      let cls = box_list [ trans_cl nspc (Binder (p, n)) ] in
      let mot = bind_var x (mk_meta nspc) in
      let n = Syntax1.(_Match (_Var x) mot cls) in
      Syntax1.(_MLet m (bind_var x n)))
  (* session *)
  | Proto -> Syntax1._Proto
  | End -> Syntax1.(_End)
  | Act (rel, rol, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.(_Act (trans_rel rel) (trans_role rol) a (bind_var x b))
  | Ch (rol, m) -> Syntax1.(_Ch (trans_role rol) (trans_tm nspc m))
  | Open prim -> Syntax1.(_Open (trans_prim prim))
  | Fork (a, Binder (id, m)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let m = trans_tm ((id, EVar x) :: nspc) m in
    Syntax1.(_Fork a (bind_var x m))
  | Recv m -> Syntax1.(_Recv (trans_tm nspc m))
  | Send m -> Syntax1.(_Send (trans_tm nspc m))
  | Close m -> Syntax1.(_Close (trans_tm nspc m))

and trans_cl nspc = function
  | Binder (PPair (rel, s, id1, id2), m) ->
    let nspc, xs = trans_xs nspc [ id1; id2 ] in
    let m = trans_tm nspc m in
    let bnd = bind_mvar (Array.of_list xs) m in
    Syntax1.(_PPair (trans_rel rel) (trans_sort nspc s) bnd)
  | Binder (PCons (id, ids), m) -> (
    match find_cons id nspc with
    | Some (c, _, _) ->
      let nspc, xs = trans_xs nspc ids in
      let m = trans_tm nspc m in
      let bnd = bind_mvar (Array.of_list xs) m in
      Syntax1.(_PCons c bnd)
    | _ -> failwith "trans_tm Match")

let rec trans_param trans nspc = function
  | PBase a -> Syntax1.(_PBase (trans nspc a), 0)
  | PBind (a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b, i = trans_param trans ((id, EVar x) :: nspc) b in
    Syntax1.(_PBind a (bind_var x b), i + 1)

let rec trans_tele nspc = function
  | TBase a -> Syntax1.(_TBase (trans_tm nspc a))
  | TBind (rel, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b = trans_tele ((id, EVar x) :: nspc) b in
    Syntax1.(_TBind (trans_rel rel) a (bind_var x b))

let rec trans_args nspc = function
  | ABase (b, m) ->
    let b = trans_tm nspc b in
    let m = trans_tm nspc m in
    (b, m)
  | ABind (rel, a, Binder (id, args)) ->
    let x = Syntax1.(V.mk id) in
    let a = trans_tm nspc a in
    let b, m = trans_args ((id, EVar x) :: nspc) args in
    Syntax1.
      ( _Pi (trans_rel rel) _U a (bind_var x b)
      , _Lam (trans_rel rel) _U (bind_var x m) )

let trans_scheme nspc trans (Binder (ids, m)) =
  let nspc, xs, i =
    List.fold_left
      (fun (nspc, xs, i) id ->
        let x = Syntax1.(SV.mk id) in
        let nspc = (id, ESVar x) :: nspc in
        (nspc, x :: xs, i + 1))
      (nspc, [], 0) ids
  in
  let m, res = trans nspc i m in
  (bind_mvar (Array.of_list (List.rev xs)) m, res)

let trans_dcons nspc (DCons (id, sch)) =
  let c = C.mk id in
  let sch, (i, j) =
    trans_scheme nspc
      (fun nspc i ptl ->
        let ptl, j = trans_param trans_tele nspc ptl in
        (ptl, (i, j)))
      sch
  in
  ((id, ECons (c, i, j)) :: nspc, Syntax1.(_DCons c sch))

let rec trans_dconss nspc = function
  | [] -> (nspc, [])
  | dcons :: dconss ->
    let nspc, dcons = trans_dcons nspc dcons in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, dcons :: dconss)

let rec trans_dcl nspc = function
  | DTm (rel, id, sch) ->
    let x = Syntax1.(V.mk id) in
    let sch, i =
      trans_scheme nspc
        (fun nspc i args ->
          let nspc = (id, EConst (x, i)) :: nspc in
          let m, a = trans_args nspc args in
          (box_pair m a, i))
        sch
    in
    let nspc = (id, EConst (x, i)) :: nspc in
    (nspc, Syntax1.(_DTm (trans_rel rel) x sch))
  | DData (id, sch, dconss) ->
    let d = D.mk id in
    let sch, i =
      trans_scheme nspc
        (fun nspc i ptm ->
          let ptm, _ = trans_param trans_tm nspc ptm in
          (ptm, i))
        sch
    in
    let nspc = (id, EData (d, i)) :: nspc in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, Syntax1._DData d sch (box_list dconss))

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
