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
      | ESVar x -> Syntax1._SVar x :: acc
      | _ -> acc)
    nspc []

let vspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | EVar x -> Syntax1._Var x :: acc
      | _ -> acc)
    nspc []

let trans_sort nspc = function
  | U -> Syntax1._U
  | L -> Syntax1._L
  | SId "_" -> Syntax1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))
  | SId id -> (
    match find_svar id nspc with
    | Some x -> Syntax1.(_SVar x)
    | None -> failwith "trans01.trans_sort(%s)" id)

let mk_smeta nspc =
  Syntax1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))

let mk_meta nspc =
  Syntax1.(
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
    Syntax1.(_Ann m a)
  (* core *)
  | Type s -> Syntax1.(_Type (trans_sort nspc s))
  | Id "_" -> mk_meta nspc
  | Id id -> (
    Syntax1.(
      match List.assoc_opt id nspc with
      | Some (EVar x) -> _Var x
      | Some (EConst (x, i)) -> _Const x (mk_inst nspc i)
      | Some (EInd (d, i, _)) -> _Ind d (mk_inst nspc i) (box []) (box [])
      | Some (EConstr (c, i, j)) ->
        _Constr c (mk_inst nspc i) (mk_param nspc j) (box [])
      | _ -> failwith "trans01.trans_tm.Id(%s)" id))
  | Inst (id, ss) -> (
    let ss = box_list (List.map (trans_sort nspc) ss) in
    Syntax1.(
      match List.assoc_opt id nspc with
      | Some (EConst (x, _)) -> _Const x ss
      | Some (EInd (d, _, _)) -> _Ind d ss (box []) (box [])
      | Some (EConstr (c, _, j)) -> _Constr c ss (mk_param nspc j) (box [])
      | _ -> failwith "trans01.trans_tm.Inst(%s)" id))
  | Pi (relv, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(Var.mk id) in
    let b = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.(_Pi (trans_relv relv) (trans_sort nspc s) a (bind_var x b))
  | Fun (a, Binder (id_opt, cls)) ->
    let a = trans_tm nspc a in
    let x, nspc =
      match id_opt with
      | Some id ->
        let x = Syntax1.(Var.mk id) in
        (x, (id, EVar x) :: nspc)
      | None -> (Syntax1.(Var.mk ""), nspc)
    in
    let cls = trans_cls nspc cls in
    Syntax1.(_Fun a (bind_var x (box_list cls)))
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      Syntax1.(
        let ms = List.map (trans_tm nspc) ms in
        match List.assoc_opt id nspc with
        | Some (EVar x) -> _mkApps (_Var x) ms
        | Some (EConst (x, i)) -> _mkApps (_Const x (mk_inst nspc i)) ms
        | Some (EInd (d, i, j)) ->
          let ms, ns = list_take j ms in
          _Ind d (mk_inst nspc i) (box_list ms) (box_list ns)
        | Some (EConstr (c, i, j)) ->
          _Constr c (mk_inst nspc i) (mk_param nspc j) (box_list ms)
        | _ -> failwith "trans01.trans_tm.App(%s)" id))
    | Inst (id, ss) :: ms -> (
      Syntax1.(
        let ss = List.map (trans_sort nspc) ss in
        let ms = List.map (trans_tm nspc) ms in
        match List.assoc_opt id nspc with
        | Some (EConst (x, _)) -> _mkApps (_Const x (box_list ss)) ms
        | Some (EInd (d, _, j)) ->
          let ms, ns = list_take j ms in
          _Ind d (box_list ss) (box_list ms) (box_list ns)
        | Some (EConstr (c, _, j)) ->
          _Constr c (box_list ss) (mk_param nspc j) (box_list ms)
        | _ -> failwith "trans01.trans_tm.Inst"))
    | m :: ms ->
      let m = trans_tm nspc m in
      let ms = List.map (trans_tm nspc) ms in
      Syntax1.(_mkApps m ms)
    | _ -> failwith "trans01.trans_tm.App")
  | Let (relv, m, Binder (id, n)) ->
    let m = trans_tm nspc m in
    let x = Syntax1.(Var.mk id) in
    let n = trans_tm ((id, EVar x) :: nspc) n in
    Syntax1.(_Let (trans_relv relv) m (bind_var x n))
  (* inductive *)
  | Match (rms, opt, cls) ->
    let ms = List.map (fun (_, m, _) -> trans_tm nspc m) rms in
    let args, nspc' =
      List.fold_left
        (fun (args, nspc) (relv, _, opt) ->
          let relv = trans_relv relv in
          match opt with
          | Some (id, a) ->
            let x = Syntax1.(Var.mk id) in
            let a = trans_tm nspc a in
            ((relv, x, a) :: args, (id, EVar x) :: nspc)
          | None ->
            let x = Syntax1.(Var.mk "") in
            let a = mk_meta nspc in
            ((relv, x, a) :: args, ("", EVar x) :: nspc))
        ([], nspc) rms
    in
    let a =
      List.fold_left
        (fun acc (relv, x, a) -> Syntax1.(_Pi relv _L a (bind_var x acc)))
        (match opt with
        | Some b -> trans_tm nspc' b
        | None -> mk_meta nspc')
        args
    in
    let cls = trans_cls nspc cls in
    Syntax1.(_Match (box_list ms) a (box_list cls))
  (* monad *)
  | IO a -> Syntax1.(_IO (trans_tm nspc a))
  | Return m -> Syntax1.(_Return (trans_tm nspc m))
  | MLet (m, Binder (id, n)) ->
    let m = trans_tm nspc m in
    let x = Syntax1.(Var.mk id) in
    let n = trans_tm ((id, EVar x) :: nspc) n in
    Syntax1.(_MLet m (bind_var x n))
  | Magic a -> Syntax1.(_Magic (trans_tm nspc a))

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
  | PId "_" -> Syntax1.([ ("", Var.mk "") ], _P0Rel)
  | PId id -> (
    Syntax1.(
      match find_constr id nspc with
      | Some (c, _, _) -> ([], _P0Mul c (box []))
      | _ -> ([ (id, Var.mk id) ], _P0Rel)))
  | PAbsurd -> Syntax1.([], _P0Absurd)
  | PMul (id, ps) -> (
    Syntax1.(
      match find_constr id nspc with
      | Some (c, _, _) ->
        let xs, ps = trans_ps nspc ps in
        (xs, _P0Mul c (box_list ps))
      | _ -> failwith "trans01.trans_p.PMul"))
  | PAdd (id, i, ps) -> (
    Syntax1.(
      match find_constr id nspc with
      | Some (c, _, _) ->
        let xs, ps = trans_ps nspc ps in
        (xs, _P0Add c i (box_list ps))
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
          let x = Syntax1.SVar.mk sid in
          (((sid, ESVar x) :: nspc, i + 1), x))
        (nspc, 0) sids
    in
    let nspc = (id, EConst (x, i)) :: nspc in
    let m = trans_tm local m in
    let a = trans_tm local a in
    let sch = bind_mvar (Array.of_list xs) (box_pair m a) in
    Syntax1.
      (nspc, Definition { name = x; relv = trans_relv relv; scheme = unbox sch })
  | Inductive { name = id; relv; body = Binder (sids, param) } ->
    let d = Ind.mk id in
    let args, tele, dconstrs = flatten_param param in
    let i = List.length sids in
    let j = List.length args in
    let arity = trans_tele nspc sids args tele in
    let nspc = (id, EInd (d, i, j)) :: nspc in
    let dconstrs = trans_dconstrs nspc sids args dconstrs in
    let (nspc, cset), dconstrs =
      List.fold_left_map
        (fun (nspc, cset) (mode, id, c, sch) ->
          let nspc = (id, EConstr (c, i, j)) :: nspc in
          let cset = Constr.Set.add c cset in
          let dconstr = Syntax1._DConstr mode c sch in
          ((nspc, cset), dconstr))
        (nspc, Constr.Set.empty) dconstrs
    in
    let dconstrs = box_list dconstrs in
    Syntax1.
      ( nspc
      , Inductive
          { name = d
          ; relv = trans_relv relv
          ; arity = unbox arity
          ; dconstrs = unbox dconstrs
          } )

and trans_dcls nspc = function
  | [] -> (nspc, [])
  | dcl :: dcls ->
    let nspc, dcl = trans_dcl nspc dcl in
    let nspc, dcls = trans_dcls nspc dcls in
    (nspc, dcl :: dcls)

and flatten_param = function
  | PBase (tele, dconstrs) -> ([], tele, dconstrs)
  | PBind (a, Binder (id, param)) ->
    let args, tele, dconstrs = flatten_param param in
    ((id, a) :: args, tele, dconstrs)

and trans_tele nspc sids args tele =
  let rec aux_args nspc = function
    | [] -> Syntax1._PBase (aux_tele nspc tele)
    | (id, a) :: args ->
      let x = Syntax1.Var.mk id in
      let a = trans_tm nspc a in
      let param = aux_args ((id, EVar x) :: nspc) args in
      Syntax1._PBind a (bind_var x param)
  and aux_tele nspc = function
    | TBase a -> Syntax1._TBase (trans_tm nspc a)
    | TBind (relv, a, Binder (id, tele)) ->
      let x = Syntax1.Var.mk id in
      let a = trans_tm nspc a in
      let tele = aux_tele ((id, EVar x) :: nspc) tele in
      Syntax1._TBind (trans_relv relv) a (bind_var x tele)
  in
  let xs = List.map Syntax1.SVar.mk sids in
  let nspc =
    List.fold_left2 (fun acc sid x -> (sid, ESVar x) :: acc) nspc sids xs
  in
  bind_mvar (Array.of_list xs) (aux_args nspc args)

and trans_dconstr nspc sids args = function
  | DMul (id, tele) ->
    let c = Constr.mk id in
    let sch = trans_tele nspc sids args tele in
    (Syntax1.Multiplicative, id, c, sch)
  | DAdd (id, tele) ->
    let c = Constr.mk id in
    let sch = trans_tele nspc sids args tele in
    (Syntax1.Additive, id, c, sch)

and trans_dconstrs nspc sids args dconstrs =
  List.map (trans_dconstr nspc sids args) dconstrs
