open Fmt
open Bindlib
open Names
open Syntax0

type nspc_entry =
  | EVar of Syntax1.tm var * view list
  | ESVar of Syntax1.sort var
  | EConst of Const.t * int * view list
  | ETName of TName.t * int * view list
  | EInd of Ind.t * int * int * view list
  | EConstr of Constr.t * int * int * view list
  | ESymbol of tm

type nspc = (int * nspc_entry) list

let nspc_assoc s (nspc : nspc) = List.assoc_opt (Hashtbl.hash s) nspc
let nspc_push s entry (nspc : nspc) = (Hashtbl.hash s, entry) :: nspc

let find_var s (nspc : nspc) =
  let s = Hashtbl.hash s in
  let opt =
    List.find_opt
      (function
        | k, EVar _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EVar (x, _)) -> Some x
  | _ -> None

let find_svar s (nspc : nspc) =
  let s = Hashtbl.hash s in
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

let find_const s (nspc : nspc) =
  let s = Hashtbl.hash s in
  let opt =
    List.find_opt
      (function
        | k, EConst _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EConst (x, _, _)) -> Some x
  | _ -> None

let find_tname s (nspc : nspc) =
  let s = Hashtbl.hash s in
  let opt =
    List.find_opt
      (function
        | k, ETName _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, ETName (x, _, _)) -> Some x
  | _ -> None

let find_ind s (nspc : nspc) =
  let s = Hashtbl.hash s in
  let opt =
    List.find_opt
      (function
        | k, EInd _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EInd (d, i, j, view)) -> Some (d, i, j, view)
  | _ -> None

let find_constr s (nspc : nspc) =
  let s = Hashtbl.hash s in
  let opt =
    List.find_opt
      (function
        | k, EConstr _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EConstr (c, i, j, view)) -> Some (c, i, j, view)
  | _ -> None

let trans_relv = function
  | R -> Syntax1.R
  | N -> Syntax1.N

let sspine_of_nspc (nspc : nspc) =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | ESVar x -> Syntax1._SVar x :: acc
      | _ -> acc)
    nspc []

let trans_sort (nspc : nspc) = function
  | U -> Syntax1._U
  | L -> Syntax1._L
  | SId "_" -> Syntax1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))
  | SId id -> (
    match find_svar id nspc with
    | Some x -> Syntax1.(_SVar x)
    | None -> failwith "trans01.trans_sort(%s)" id)

let mk_smeta (nspc : nspc) =
  Syntax1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))

let mk_meta () = Syntax1.(_IMeta (IMeta.mk "") (box []) (box []))

let mk_inst nspc i =
  let ss = List.init i (fun _ -> mk_smeta nspc) in
  box_list ss

let mk_param i =
  let ms = List.init i (fun _ -> mk_meta ()) in
  box_list ms

let rec list_take i ms =
  match (i, ms) with
  | 0, ms -> ([], ms)
  | _, m :: ms ->
    let ms, ns = list_take (i - 1) ms in
    (m :: ms, ns)
  | _ -> (ms, [])

let rec inject_implicit (nspc : nspc) view ms =
  match (view, ms) with
  | [], _ -> ms
  | E :: view, m :: ms -> m :: inject_implicit nspc view ms
  | E :: view, [] -> failwith "trans01.inject_view"
  | I :: view, _ -> mk_meta () :: inject_implicit nspc view ms

let rec trans_tm (nspc : nspc) = function
  (* inference *)
  | Ann (m, a) ->
    let m = trans_tm nspc m in
    let a = trans_tm nspc a in
    Syntax1.(_Ann m a)
  | IMeta -> mk_meta ()
  (* core *)
  | Type s -> Syntax1.(_Type (trans_sort nspc s))
  | Id ("_", _) -> mk_meta ()
  | Id (id, _) -> (
    Syntax1.(
      match nspc_assoc id nspc with
      | Some (EVar (x, _)) -> _Var x
      | Some (EConst (x, i, _)) -> _Const x (mk_inst nspc i)
      | Some (ETName (x, i, _)) -> _TName x (mk_inst nspc i)
      | Some (EInd (d, i, _, _)) -> _Ind d (mk_inst nspc i) (box []) (box [])
      | Some (EConstr (c, i, j, _)) ->
        _Constr c (mk_inst nspc i) (mk_param j) (box [])
      | _ -> failwith "trans01.trans_tm.Id(%s)" id))
  | Inst (id, ss, _) -> (
    let ss = box_list (List.map (trans_sort nspc) ss) in
    Syntax1.(
      match nspc_assoc id nspc with
      | Some (EConst (x, _, _)) -> _Const x ss
      | Some (ETName (x, _, _)) -> _TName x ss
      | Some (EInd (d, _, _, _)) -> _Ind d ss (box []) (box [])
      | Some (EConstr (c, _, j, _)) -> _Constr c ss (mk_param j) (box [])
      | _ -> failwith "trans01.trans_tm.Inst(%s)" id))
  | Pi (relv, s, a, Binder (id, b)) ->
    let a = trans_tm nspc a in
    let x = Syntax1.(Var.mk id) in
    let b = trans_tm (nspc_push id (EVar (x, [])) nspc) b in
    Syntax1.(_Pi (trans_relv relv) (trans_sort nspc s) a (bind_var x b))
  | Fun (a, Binder (id_opt, cls), view) ->
    let a = trans_tm nspc a in
    let x, nspc =
      match id_opt with
      | Some id ->
        let x = Syntax1.(Var.mk id) in
        (x, nspc_push id (EVar (x, view)) nspc)
      | None -> (Syntax1.(Var.mk ""), nspc)
    in
    let guard, cls = trans_cls nspc cls in
    Syntax1.(_Fun guard a (bind_var x (box_list cls)))
  | App ms -> (
    match ms with
    | Id (id, E) :: ms -> (
      Syntax1.(
        let ms = List.map (trans_tm nspc) ms in
        match nspc_assoc id nspc with
        | Some (EVar (x, _)) -> _mkApps (_Var x) ms
        | Some (EConst (x, i, _)) -> _mkApps (_Const x (mk_inst nspc i)) ms
        | Some (ETName (x, i, _)) -> _mkApps (_TName x (mk_inst nspc i)) ms
        | Some (EInd (d, i, j, _)) ->
          let ms, ns = list_take j ms in
          _Ind d (mk_inst nspc i) (box_list ms) (box_list ns)
        | Some (EConstr (c, i, j, _)) ->
          let ms, ns = list_take j ms in
          _Constr c (mk_inst nspc i) (box_list ms) (box_list ns)
        | _ -> failwith "trans01.trans_tm.App(%s)" id))
    | Id (id, I) :: ms -> (
      Syntax1.(
        let ms = List.map (trans_tm nspc) ms in
        match nspc_assoc id nspc with
        | Some (EVar (x, view)) ->
          let ms = inject_implicit nspc view ms in
          _mkApps (_Var x) ms
        | Some (EConst (x, i, view)) ->
          let ms = inject_implicit nspc view ms in
          _mkApps (_Const x (mk_inst nspc i)) ms
        | Some (ETName (x, i, view)) ->
          let ms = inject_implicit nspc view ms in
          _mkApps (_TName x (mk_inst nspc i)) ms
        | Some (EInd (d, i, j, view)) ->
          let ms, ns = list_take j (inject_implicit nspc view ms) in
          _Ind d (mk_inst nspc i) (box_list ms) (box_list ns)
        | Some (EConstr (c, i, j, view)) ->
          let ms = inject_implicit nspc view ms in
          _Constr c (mk_inst nspc i) (mk_param j) (box_list ms)
        | _ -> failwith "trans01.trans_tm.App(%s)" id))
    | Inst (id, ss, E) :: ms -> (
      Syntax1.(
        let ss = List.map (trans_sort nspc) ss in
        let ms = List.map (trans_tm nspc) ms in
        match nspc_assoc id nspc with
        | Some (EConst (x, _, _)) -> _mkApps (_Const x (box_list ss)) ms
        | Some (ETName (x, _, _)) -> _mkApps (_TName x (box_list ss)) ms
        | Some (EInd (d, _, j, _)) ->
          let ms, ns = list_take j ms in
          _Ind d (box_list ss) (box_list ms) (box_list ns)
        | Some (EConstr (c, _, j, _)) ->
          let ms, ns = list_take j ms in
          _Constr c (box_list ss) (box_list ms) (box_list ns)
        | _ -> failwith "trans01.trans_tm.Inst"))
    | Inst (id, ss, I) :: ms -> (
      Syntax1.(
        let ss = List.map (trans_sort nspc) ss in
        let ms = List.map (trans_tm nspc) ms in
        match nspc_assoc id nspc with
        | Some (EConst (x, _, view)) ->
          let ms = inject_implicit nspc view ms in
          _mkApps (_Const x (box_list ss)) ms
        | Some (ETName (x, _, view)) ->
          let ms = inject_implicit nspc view ms in
          _mkApps (_TName x (box_list ss)) ms
        | Some (EInd (d, _, j, view)) ->
          let ms, ns = list_take j (inject_implicit nspc view ms) in
          _Ind d (box_list ss) (box_list ms) (box_list ns)
        | Some (EConstr (c, _, j, view)) ->
          let ms = inject_implicit nspc view ms in
          _Constr c (box_list ss) (mk_param j) (box_list ms)
        | _ -> failwith "trans01.trans_tm.Inst"))
    | m :: ms ->
      let m = trans_tm nspc m in
      let ms = List.map (trans_tm nspc) ms in
      Syntax1.(_mkApps m ms)
    | _ -> failwith "trans01.trans_tm.App")
  | Let (relv, m, Binder (p0, n)) -> (
    let m = trans_tm nspc m in
    let _, p, _ = trans_p nspc p0 in
    let r = trans_relv relv in
    match (p0, unbox p) with
    | PId id, Syntax1.P0Rel ->
      let x = Syntax1.(Var.mk id) in
      let n = trans_tm (nspc_push id (EVar (x, [])) nspc) n in
      Syntax1.(_Let r m (bind_var x n))
    | _ ->
      let x = Syntax1.Var.mk "" in
      let guard, cls = trans_cls nspc [ ([ p0 ], Some n) ] in
      let a = Syntax1.(_Pi r _L (mk_meta ()) (bind_var x (mk_meta ()))) in
      Syntax1.(_Match guard (box_list [ m ]) a (box_list cls)))
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
            ((relv, x, a) :: args, nspc_push id (EVar (x, [])) nspc)
          | None ->
            let x = Syntax1.(Var.mk "") in
            let a = mk_meta () in
            ((relv, x, a) :: args, nspc_push "" (EVar (x, [])) nspc))
        ([], nspc) rms
    in
    let a =
      List.fold_left
        (fun acc (relv, x, a) -> Syntax1.(_Pi relv _L a (bind_var x acc)))
        (match opt with
        | Some b -> trans_tm nspc' b
        | None -> mk_meta ())
        args
    in
    let guard, cls = trans_cls nspc cls in
    Syntax1.(_Match guard (box_list ms) a (box_list cls))
  (* monad *)
  | IO a -> Syntax1.(_IO (trans_tm nspc a))
  | Return m -> Syntax1.(_Return (trans_tm nspc m))
  | MLet (m, Binder (p0, n)) -> (
    let m = trans_tm nspc m in
    let _, p, _ = trans_p nspc p0 in
    match (p0, unbox p) with
    | PId id, Syntax1.P0Rel ->
      let x = Syntax1.Var.mk id in
      let n = trans_tm (nspc_push id (EVar (x, [])) nspc) n in
      Syntax1.(_MLet m (bind_var x n))
    | _ ->
      let x = Syntax1.Var.mk "" in
      let ms = box_list [ Syntax1._Var x ] in
      let guard, cls = trans_cls nspc [ ([ p0 ], Some n) ] in
      let a = Syntax1.(_Pi R _L (mk_meta ()) (bind_var x (mk_meta ()))) in
      Syntax1.(_MLet m (bind_var x (_Match guard ms a (box_list cls)))))
  (* custom *)
  | UOpr (sym, m) -> (
    match nspc_assoc sym nspc with
    | Some (ESymbol body) -> trans_tm nspc (subst_hole [| m |] body)
    | _ -> failwith "trans01.trans_tm(UOpr %s)" sym)
  | BOpr (sym, m, n) -> (
    match nspc_assoc sym nspc with
    | Some (ESymbol body) -> trans_tm nspc (subst_hole [| m; n |] body)
    | _ -> failwith "trans01.trans_tm(BOpr %s)" sym)
  | Hole i -> failwith "trans01.trans_tm(Hole %%%d)" i
  | Magic a -> Syntax1.(_Magic (trans_tm nspc a))

and trans_cls nspc cls =
  let rec merge_guard xs ys =
    match (xs, ys) with
    | x :: xs, y :: ys -> (x || y) :: merge_guard xs ys
    | [], _ -> ys
    | _, [] -> xs
  in
  List.fold_left_map
    (fun acc (ps, opt) ->
      match ps with
      | [] -> failwith "trans01.trans_cls"
      | _ ->
        let args, ps, guard = trans_ps nspc ps in
        let nspc =
          List.fold_left
            (fun acc (id, x) -> nspc_push id (EVar (x, [])) acc)
            nspc args
        in
        let xs = List.map (fun (_, x) -> x) args in
        let opt = Option.map (trans_tm nspc) opt in
        ( merge_guard guard acc
        , box_pair (box_list ps) (bind_mvar (Array.of_list xs) (box_opt opt)) ))
    [] cls

and trans_p nspc p =
  let rec p_of_tm = function
    | App (Id (id, _) :: ms) -> PConstr (id, List.map p_of_tm ms)
    | App (Inst (id, _, _) :: ms) -> PConstr (id, List.map p_of_tm ms)
    | Hole i -> PHole i
    | UOpr (sym, m) -> PUOpr (sym, p_of_tm m)
    | BOpr (sym, m, n) -> PBOpr (sym, p_of_tm m, p_of_tm n)
    | m -> failwith "trans01.p_of_tm(%a)" pp_tm m
  in
  match p with
  | PId "_" -> Syntax1.([ ("", Var.mk "") ], _P0Rel, false)
  | PId id -> (
    Syntax1.(
      match find_constr id nspc with
      | Some (c, _, _, _) -> ([], _P0Constr c (box []), true)
      | _ -> ([ (id, Var.mk id) ], _P0Rel, false)))
  | PAbsurd -> Syntax1.([], _P0Absurd, false)
  | PConstr (id, ps) -> (
    Syntax1.(
      match find_constr id nspc with
      | Some (c, _, _, _) ->
        let xs, ps, _ = trans_ps nspc ps in
        (xs, _P0Constr c (box_list ps), true)
      | _ -> failwith "trans01.trans_p(Constr(%a))" pp_p p))
  | PBOpr (sym, p1, p2) -> (
    match nspc_assoc sym nspc with
    | Some (ESymbol body) ->
      let p0 = p_of_tm body in
      trans_p nspc (subst_phole [| p1; p2 |] p0)
    | _ -> failwith "trans01.trans_p(PBOpr(%s))" sym)
  | PUOpr (sym, p1) -> (
    match nspc_assoc sym nspc with
    | Some (ESymbol body) ->
      let p0 = p_of_tm body in
      trans_p nspc (subst_phole [| p1 |] p0)
    | _ -> failwith "trans01.trans_p(PBOpr(%s))" sym)
  | PHole i -> failwith "trans01.trans_p(PHole %%%d)" i

and trans_ps nspc ps =
  let xs, pg =
    List.fold_left_map
      (fun acc p ->
        let xs, p, guard = trans_p nspc p in
        (acc @ xs, (p, guard)))
      [] ps
  in
  let ps, guard = List.split pg in
  (xs, ps, guard)

let rec trans_dcl nspc = function
  | Definition { name = id; relv; body = Binder (sids, (m, a)); view } ->
    let x = Const.mk id in
    let (local, i), xs =
      List.fold_left_map
        (fun (nspc, i) sid ->
          let x = Syntax1.SVar.mk sid in
          ((nspc_push sid (ESVar x) nspc, i + 1), x))
        (nspc, 0) sids
    in
    let nspc = nspc_push id (EConst (x, i, view)) nspc in
    let m = trans_tm local m in
    let a = trans_tm local a in
    let sch = bind_mvar (Array.of_list xs) (box_pair m a) in
    Syntax1.
      ( nspc
      , [ Definition { name = x; relv = trans_relv relv; scheme = unbox sch } ]
      )
  | Inductive { name = id; relv; body = Binder (sids, param); view } ->
    let d = Ind.mk id in
    let args, tele, dconstrs = flatten_param param in
    let i = List.length sids in
    let j = List.length args in
    let arity = trans_tele nspc sids args tele in
    let nspc = nspc_push id (EInd (d, i, j, view)) nspc in
    let dconstrs = trans_dconstrs nspc sids args dconstrs in
    let (nspc, cset), dconstrs =
      List.fold_left_map
        (fun (nspc, cset) (id, c, sch, view) ->
          let nspc = nspc_push id (EConstr (c, i, j, view)) nspc in
          let cset = Constr.Set.add c cset in
          let dconstr = Syntax1._DConstr c sch in
          ((nspc, cset), dconstr))
        (nspc, Constr.Set.empty) dconstrs
    in
    let dconstrs = box_list dconstrs in
    Syntax1.
      ( nspc
      , [ Inductive
            { name = d
            ; relv = trans_relv relv
            ; arity = unbox arity
            ; dconstrs = unbox dconstrs
            }
        ] )
  | Template { name = id; relv; body = Binder (sids, a); view } ->
    let x = TName.mk id in
    let (local, i), xs =
      List.fold_left_map
        (fun (nspc, i) sid ->
          let x = Syntax1.SVar.mk sid in
          ((nspc_push sid (ESVar x) nspc, i + 1), x))
        (nspc, 0) sids
    in
    let nspc = nspc_push id (ETName (x, i, view)) nspc in
    let a = trans_tm local a in
    let sch = bind_mvar (Array.of_list xs) a in
    Syntax1.
      ( nspc
      , [ Template { name = x; relv = trans_relv relv; scheme = unbox sch } ] )
  | Implement { name = id; relv; body = Binder (sids, (m, a)); view } ->
    failwith "unimplemented"
  | Extern { name = id; relv; body = Binder (sids, (m_opt, a)); view } ->
    let x = Const.mk id in
    let (local, i), xs =
      List.fold_left_map
        (fun (nspc, i) sid ->
          let x = Syntax1.SVar.mk sid in
          ((nspc_push sid (ESVar x) nspc, i + 1), x))
        (nspc, 0) sids
    in
    let nspc = nspc_push id (EConst (x, i, view)) nspc in
    let m_opt = box_opt (Option.map (trans_tm local) m_opt) in
    let a = trans_tm local a in
    let sch = bind_mvar (Array.of_list xs) (box_pair m_opt a) in
    Syntax1.
      (nspc, [ Extern { name = x; relv = trans_relv relv; scheme = unbox sch } ])
  | Notation { name = sym; body } ->
    let nspc = nspc_push sym (ESymbol body) nspc in
    Syntax1.(nspc, [])

and trans_dcls nspc = function
  | [] -> (nspc, [])
  | dcl :: dcls ->
    let nspc, dcl = trans_dcl nspc dcl in
    let nspc, dcls = trans_dcls nspc dcls in
    (nspc, dcl @ dcls)

and flatten_param = function
  | PBase (tele, dconstrs) -> ([], tele, dconstrs)
  | PBind (a, Binder (id, param)) ->
    let args, tele, dconstrs = flatten_param param in
    ((id, a) :: args, tele, dconstrs)

and trans_tele (nspc : nspc) sids args tele =
  let rec aux_args nspc = function
    | [] -> Syntax1._PBase (aux_tele nspc tele)
    | (id, a) :: args ->
      let x = Syntax1.Var.mk id in
      let a = trans_tm nspc a in
      let param = aux_args (nspc_push id (EVar (x, [])) nspc) args in
      Syntax1._PBind a (bind_var x param)
  and aux_tele nspc = function
    | TBase a -> Syntax1._TBase (trans_tm nspc a)
    | TBind (relv, a, Binder (id, tele)) ->
      let x = Syntax1.Var.mk id in
      let a = trans_tm nspc a in
      let tele = aux_tele (nspc_push id (EVar (x, [])) nspc) tele in
      Syntax1._TBind (trans_relv relv) a (bind_var x tele)
  in
  let xs = List.map Syntax1.SVar.mk sids in
  let nspc =
    List.fold_left2 (fun acc sid x -> nspc_push sid (ESVar x) acc) nspc sids xs
  in
  bind_mvar (Array.of_list xs) (aux_args nspc args)

and trans_dconstr (nspc : nspc) sids args = function
  | DConstr (id, tele, view) ->
    let c = Constr.mk id in
    let sch = trans_tele nspc sids args tele in
    (id, c, sch, view)

and trans_dconstrs (nspc : nspc) sids args dconstrs =
  List.map (trans_dconstr nspc sids args) dconstrs
