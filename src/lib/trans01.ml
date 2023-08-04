open Fmt
open Bindlib
open Names
open Syntax0

type nspc_entry =
  | EVar of Syntax1.tm var
  | ESVar of Syntax1.sort var
  | EConst of Const.t * int
  | EInd of Ind.t * int * int
  | EConstr of Constr.t * int * int

type nspc = (string * nspc_entry) list

let find_var s nspc =
  let opt =
    List.find_opt
      (function
        | k, EVar _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EVar x) -> Some x
  | _ -> None

let find_svar s nspc =
  let opt =
    List.find_opt
      (function
        | k, ESVar _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, ESVar x) -> Some x
  | _ -> None

let find_const s nspc =
  let opt =
    List.find_opt
      (function
        | k, EConst _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EConst (x, _)) -> Some x
  | _ -> None

let find_ind s nspc =
  let opt =
    List.find_opt
      (function
        | k, EInd _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EInd (d, i, j)) -> Some (d, i, j)
  | _ -> None

let find_constr s nspc =
  let opt =
    List.find_opt
      (function
        | k, EConstr _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EConstr (c, i, j)) -> Some (c, i, j)
  | _ -> None

let trans_relv = function
  | R -> Syntax1.R
  | N -> Syntax1.N

let sspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | ESVar x -> Binding1._SVar x :: acc
      | _ -> acc)
    nspc []

let vspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | EVar x -> Binding1._Var x :: acc
      | _ -> acc)
    nspc []

let trans_sort nspc = function
  | U -> Binding1._U
  | L -> Binding1._L
  | SId "_" -> Binding1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))
  | SId id -> (
    match find_svar id nspc with
    | Some x -> Binding1.(_SVar x)
    | None -> failwith "trans01.trans_sort")

let mk_smeta nspc =
  Binding1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))

let mk_meta nspc =
  Binding1.(
    _IMeta (IMeta.mk "")
      (box_list (sspine_of_nspc nspc))
      (box_list (vspine_of_nspc nspc)))

let mk_inst nspc i =
  let ss = List.init i (fun _ -> mk_smeta nspc) in
  box_list ss

let mk_param nspc i =
  let ms = List.init i (fun _ -> mk_meta nspc) in
  box_list ms

let rec list_take i ms =
  match (i, ms) with
  | 0, ms -> ([], ms)
  | _, m :: ms ->
    let ms, ns = list_take (i - 1) ms in
    (m :: ms, ns)
  | _ -> (ms, [])

let rec trans_tm nspc = function
  (* inference *)
  | Ann (m, a) ->
    let m = trans_tm nspc m in
    let a = trans_tm nspc a in
    Binding1.(_Ann m a)
  (* core *)
  | Type s -> Binding1.(_Type (trans_sort nspc s))
  | Id "_" -> mk_meta nspc
  | Id id -> (
    Binding1.(
      match List.assoc_opt id nspc with
      | Some (EVar x) -> _Var x
      | Some (EConst (x, i)) -> _Const x (mk_inst nspc i)
      | Some (EInd (ind, i, _)) -> _Ind ind (mk_inst nspc i) (box []) (box [])
      | Some (EConstr (constr, i, j)) ->
        _Constr constr (mk_inst nspc i) (mk_param nspc j) (box [])
      | _ -> failwith "trans01.trans_tm.Id(%s)" id))
  | Inst (id, ss) -> (
    let ss = box_list (List.map (trans_sort nspc) ss) in
    Binding1.(
      match List.assoc_opt id nspc with
      | Some (EConst (x, _)) -> _Const x ss
      | Some (EInd (ind, _, _)) -> _Ind ind ss (box []) (box [])
      | Some (EConstr (constr, _, j)) ->
        _Constr constr ss (mk_param nspc j) (box [])
      | _ -> failwith "trans01.trans_tm.Inst(%s)" id))
  | Pi (relv, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Binding1.(Var.mk id) in
    let b = trans_tm ((id, EVar x) :: nspc) b in
    Binding1.(_Pi (trans_relv relv) (trans_sort nspc s) a (bind_var x b))
  | Fun (a, Binder (id_opt, cls)) ->
    let a = trans_tm nspc a in
    let x, nspc =
      match id_opt with
      | Some id ->
        let x = Binding1.(Var.mk id) in
        (x, (id, EVar x) :: nspc)
      | None -> (Binding1.(Var.mk ""), nspc)
    in
    let cls = trans_cls nspc cls in
    Binding1.(_Fun a (bind_var x (box_list cls)))
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      Binding1.(
        let ms = List.map (trans_tm nspc) ms in
        match List.assoc_opt id nspc with
        | Some (EVar x) -> _mkApps (_Var x) ms
        | Some (EConst (x, i)) -> _mkApps (_Const x (mk_inst nspc i)) ms
        | Some (EInd (ind, i, j)) ->
          let ms, ns = list_take j ms in
          _Ind ind (mk_inst nspc i) (box_list ms) (box_list ns)
        | Some (EConstr (constr, i, j)) ->
          _Constr constr (mk_inst nspc i) (mk_param nspc j) (box_list ms)
        | _ -> failwith "trans01.trans_tm.App(%s)" id))
    | Inst (id, ss) :: ms -> (
      Binding1.(
        let ss = List.map (trans_sort nspc) ss in
        let ms = List.map (trans_tm nspc) ms in
        match List.assoc_opt id nspc with
        | Some (EConst (x, _)) -> _mkApps (_Const x (box_list ss)) ms
        | Some (EInd (ind, _, j)) ->
          let ms, ns = list_take j ms in
          _Ind ind (box_list ss) (box_list ms) (box_list ns)
        | Some (EConstr (constr, _, j)) ->
          _Constr constr (box_list ss) (mk_param nspc j) (box_list ms)
        | _ -> failwith "trans01.trans_tm.Inst"))
    | m :: ms ->
      let m = trans_tm nspc m in
      let ms = List.map (trans_tm nspc) ms in
      Binding1.(_mkApps m ms)
    | _ -> failwith "trans01.trans_tm.App")
  | Let (relv, m, Binder (id, n)) ->
    let m = trans_tm nspc m in
    let x = Binding1.(Var.mk id) in
    let n = trans_tm ((id, EVar x) :: nspc) n in
    Binding1.(_Let (trans_relv relv) m (bind_var x n))
  (* inductive *)
  | Match (rms, opt, cls) ->
    let ms = List.map (fun (_, m, _) -> trans_tm nspc m) rms in
    let args, nspc' =
      List.fold_left
        (fun (args, nspc) (relv, _, opt) ->
          let relv = trans_relv relv in
          match opt with
          | Some (id, a) ->
            let x = Binding1.(Var.mk id) in
            let a = trans_tm nspc a in
            ((relv, x, a) :: args, (id, EVar x) :: nspc)
          | None ->
            let x = Binding1.(Var.mk "") in
            let a = mk_meta nspc in
            ((relv, x, a) :: args, ("", EVar x) :: nspc))
        ([], nspc) rms
    in
    let a =
      List.fold_left
        (fun acc (relv, x, a) -> Binding1.(_Pi relv _L a (bind_var x acc)))
        (match opt with
        | Some b -> trans_tm nspc' b
        | None -> mk_meta nspc')
        args
    in
    let cls = trans_cls nspc cls in
    Binding1.(_Match (box_list ms) a (box_list cls))
  (* monad *)
  | IO a -> Binding1.(_IO (trans_tm nspc a))
  | Return m -> Binding1.(_Return (trans_tm nspc m))
  | MLet (m, Binder (id, n)) ->
    let m = trans_tm nspc m in
    let x = Binding1.(Var.mk id) in
    let n = trans_tm ((id, EVar x) :: nspc) n in
    Binding1.(_MLet m (bind_var x n))
  | Magic a -> Binding1.(_Magic (trans_tm nspc a))

and trans_cls nspc cls =
  List.map
    (fun (ps, opt) ->
      match ps with
      | [] -> failwith "trans01.trans_cls"
      | _ ->
        let args, ps = trans_ps nspc ps in
        let nspc =
          List.fold_left (fun acc (id, x) -> (id, EVar x) :: acc) nspc args
        in
        let xs = List.map (fun (_, x) -> x) args in
        let opt = Option.map (trans_tm nspc) opt in
        box_pair (box_list ps) (bind_mvar (Array.of_list xs) (box_opt opt)))
    cls

and trans_p nspc p =
  match p with
  | PId "_" -> Binding1.([ ("", Var.mk "") ], _P0Rel)
  | PId id -> (
    Binding1.(
      match find_constr id nspc with
      | Some (constr, _, _) -> ([], _P0Mul constr (box []))
      | _ -> ([ (id, Var.mk id) ], _P0Rel)))
  | PAbsurd -> Binding1.([], _P0Absurd)
  | PMul (id, ps) -> (
    Binding1.(
      match find_constr id nspc with
      | Some (constr, _, _) ->
        let xs, ps = trans_ps nspc ps in
        (xs, _P0Mul constr (box_list ps))
      | _ -> failwith "trans01.trans_p.PMul"))
  | PAdd (id, i, ps) -> (
    Binding1.(
      match find_constr id nspc with
      | Some (constr, _, _) ->
        let xs, ps = trans_ps nspc ps in
        (xs, _P0Add constr i (box_list ps))
      | _ -> failwith "trans01.trans_p.PAdd"))

and trans_ps nspc ps =
  List.fold_left_map
    (fun acc p ->
      let xs, p = trans_p nspc p in
      (acc @ xs, p))
    [] ps

let rec trans_dcl nspc = function
  | Definition { name = id; relv; body = Binder (sids, (m, a)) } ->
    let x = Const.mk id in
    let (local, i), xs =
      List.fold_left_map
        (fun (nspc, i) sid ->
          let x = Binding1.SVar.mk id in
          (((sid, ESVar x) :: nspc, i + 1), x))
        (nspc, 0) sids
    in
    let nspc = (id, EConst (x, i)) :: nspc in
    let m = trans_tm local m in
    let a = trans_tm local a in
    let sch = bind_mvar (Array.of_list xs) (box_pair m a) in
    Syntax1.
      (nspc, Definition { name = x; relv = trans_relv relv; body = unbox sch })
  | Inductive { name = id; relv; body = Binder (sids, param) } ->
    let ind = Ind.mk id in
    let (local, i), xs =
      List.fold_left_map
        (fun (nspc, i) sid ->
          let x = Binding1.SVar.mk sid in
          (((sid, ESVar x) :: nspc, i + 1), x))
        (nspc, 0) sids
    in
    let nspc_ext, param = trans_param id ind i local param in
    let sch = bind_mvar (Array.of_list xs) param in
    Syntax1.
      ( nspc_ext @ nspc
      , Inductive { name = ind; relv = trans_relv relv; body = unbox sch } )

and trans_dcls nspc = function
  | [] -> (nspc, [])
  | dcl :: dcls ->
    let nspc, dcl = trans_dcl nspc dcl in
    let nspc, dcls = trans_dcls nspc dcls in
    (nspc, dcl :: dcls)

and trans_param id ind i nspc param =
  let rec aux j nspc = function
    | PBase (tele, dconstrs) ->
      let tele = trans_tele nspc tele in
      let nspc_ext, dconstrs =
        trans_dconstrs i j ((id, EInd (ind, i, j)) :: nspc) dconstrs
      in
      let nspc_ext = (id, EInd (ind, i, j)) :: nspc_ext in
      Binding1.(nspc_ext, _PBase (box_pair tele (box_list dconstrs)))
    | PBind (a, Binder (id, param)) ->
      let a = trans_tm nspc a in
      let x = Binding1.Var.mk id in
      let nspc_ext, param = aux (j + 1) ((id, EVar x) :: nspc) param in
      Binding1.(nspc_ext, _PBind a (bind_var x param))
  in
  aux 0 nspc param

and trans_tele nspc = function
  | TBase a -> Binding1._TBase (trans_tm nspc a)
  | TBind (relv, a, Binder (id, tele)) ->
    let a = trans_tm nspc a in
    let x = Binding1.Var.mk id in
    let tele = trans_tele ((id, EVar x) :: nspc) tele in
    Binding1._TBind (trans_relv relv) a (bind_var x tele)

and trans_dconstrs i j nspc = function
  | [] -> ([], [])
  | DMul (id, tele) :: dconstrs ->
    let constr = Constr.mk id in
    let tele = trans_tele nspc tele in
    let nspc_ext, dconstrs = trans_dconstrs i j nspc dconstrs in
    Binding1.
      ((id, EConstr (constr, i, j)) :: nspc_ext, _DMul constr tele :: dconstrs)
  | DAdd (id, tele) :: dconstrs ->
    let constr = Constr.mk id in
    let tele = trans_tele nspc tele in
    let nspc_ext, dconstrs = trans_dconstrs i j nspc dconstrs in
    Binding1.
      ((id, EConstr (constr, i, j)) :: nspc_ext, _DAdd constr tele :: dconstrs)
