open Fmt
open Bindlib
open Names
open Syntax2
open Pprint2
open Context23

let rec gather_mlet = function
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let xs, n = gather_mlet n in
    ((x, m) :: xs, n)
  | m -> ([], m)

let trans_sort = function
  | U -> Syntax3.U
  | L -> Syntax3.L

let trans_relv = function
  | R -> Syntax3.R
  | N -> Syntax3.N

let trans_var x = Syntax3.(copy_var x var (name_of x))

let rec trans_tm ctx = function
  (* core *)
  | Var x -> Syntax3.(_Var (trans_var x))
  | Const x -> Syntax3.(_Const x)
  | Fun (relvs, bnd) ->
    let x, bnd = unbind bnd in
    let xs, m = unmbind bnd in
    let m_elab = trans_tm ctx m in
    let m_elab = List.fold_right2 (fun (relv, s) x m_elab ->
        let x = trans_var x in
        Syntax3.(_Lam (trans_sort s) (bind_var x m_elab)))
        relvs (Array.to_list xs) m_elab
    in
    Syntax3.(_Fun (bind_var (trans_var x) m_elab))
  | App (s, m, n) ->
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_App (trans_sort s) m n)
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Let m (bind_var (trans_var x) n))
  (* inductive *)
  | Constr (c, ms) ->
    let entry = Ctx.find_constr c ctx in
    let ms = List.(filter_map (function
        | N, _ -> None
        | R, m -> Some (trans_tm ctx m))
        (combine entry.layout ms))
    in
    (match (ms, entry.unbox) with
     | [], true -> Syntax3.(_Constr0 c)
     | [ m ], true -> m
     | ms, _ -> Syntax3.(_Constr1 c (box_list ms)))
  | Match (_, s, m, cls) ->
    let m = trans_tm ctx m in
    let cls = List.map (fun (c, bnd) ->
        let xs, rhs = unmbind bnd in
        let entry = Ctx.find_constr c ctx in
        let xs = List.(filter_map (function
            | N, _ -> None
            | R, x -> Some (trans_var x))
            (combine entry.layout (Array.to_list xs)))
        in (c, xs, trans_tm ctx rhs, entry.unbox))
        cls
    in
    (match cls with
     | [ (c, [ x ], rhs, true) ] ->
       let bnd = unbox (bind_var x rhs) in
       Syntax3.(lift_tm (subst bnd (unbox m)))
     | _ when List.for_all (fun (_, xs, _, unbox) -> xs = [] && unbox) cls ->
       let cls = List.map (fun (c, _, rhs, _) -> _PConstr c rhs) cls in
       Syntax3.(_Match0 m (box_list cls))
     | _ ->
       let cls = List.map (fun (c, xs, rhs, _) ->
           let xs = Array.of_list xs in
           _PConstr c (bind_mvar xs rhs))
           cls
       in Syntax3.(_Match1 (trans_sort s) m (box_list cls)))
  | Absurd -> Syntax3._Absurd
  (* monad *)
  | Return m -> Syntax3.(_Lazy (trans_tm ctx m))
  | MLet _ as m ->
    let xs, n = gather_mlet m in
    let n = List.fold_right (fun (x, m) n ->
        let x = trans_var x in
        let m = trans_tm ctx m in
        let bnd = bind_var x n in
        Syntax3.(_Let (_Force m) bnd))
        xs Syntax3.(_Force (trans_tm ctx n))
    in
    Syntax3.(_Lazy n)
  (* primitive terms *)
  | Int i -> Syntax3.(_Int i)
  | Char c -> Syntax3.(_Char c)
  | String s -> Syntax3.(_String s)
  (* primitive operators *)
  | Neg m -> Syntax3.(_Neg (trans_tm ctx m))
  | Add (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Add m n)
  | Sub (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Sub m n)
  | Mul (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Mul m n)
  | Div (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Div m n)
  | Mod (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Mod m n)
  | Lte (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Lte m n)
  | Gte (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Gte m n)
  | Lt (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Lt m n)
  | Gt (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Gt m n)
  | Eq (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Eq m n)
  | Chr m -> Syntax3.(_Chr (trans_tm ctx m))
  | Ord m -> Syntax3.(_Ord (trans_tm ctx m))
  | Push (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Push m n)
  | Cat (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Cat m n)
  | Size m -> Syntax3.(_Size (trans_tm ctx m))
  | Indx (m, n) -> 
    let m = trans_tm ctx m in
    let n = trans_tm ctx n in
    Syntax3.(_Indx m n)
  (* primitive effects *)
  | Print m ->
    let m = trans_tm ctx m in
    Syntax3.(_Lazy (_Print m))
  | Prerr m ->
    let m = trans_tm ctx m in
    Syntax3.(_Lazy (_Prerr m))
  | ReadLn m ->
    let m = trans_tm ctx m in
    Syntax3.(_Lazy (_ReadLn m))
  | Fork m ->
    let m = trans_tm ctx m in
    Syntax3.(_Lazy (_Fork m))
  | Send (R, _, m) ->
    let x = Syntax3.(Var.mk "x") in
    let m = Syntax3.(_Lazy (_Send (trans_tm ctx m) (_Var x))) in
    Syntax3.(_Lam U (bind_var x m))
  | Send (N, _, m) ->
    let x = Syntax3.(Var.mk "x") in
    let m = Syntax3.(_Lazy (trans_tm ctx m)) in
    Syntax3.(_Lam U (bind_var x m))
  | Recv (R, s, m) ->
    Syntax3.(_Lazy (_Recv (trans_sort s) (trans_tm ctx m)))
  | Recv (N, _, m) ->
    Syntax3.(_Lazy (trans_tm ctx m))
  | Close (role, m) ->
    Syntax3.(_Lazy (_Close role (trans_tm ctx m)))
  (* erasure *)
  | NULL -> Syntax3._NULL
  (* magic *)
  | Magic -> Syntax3._Magic

let trans_dcls dcls =
  let rec aux ctx = function
    | [] -> []
    | Main { body } :: dcls ->
      let body = unbox (trans_tm ctx body) in
      Syntax3.(Main { body } :: aux ctx dcls)
    | Definition { name; relv = N; body } :: dcls -> aux ctx dcls
    | Definition { name; relv = R; body } :: dcls ->
      let body = unbox (trans_tm ctx body) in
      Syntax3.(Definition { name; body } :: aux ctx dcls)
    | Inductive { name; relv; body = dconstrs } :: dcls ->
      let ctx = trans_dconstrs ctx dconstrs in
      aux ctx dcls
    | Extern { name; relv } :: dcls -> aux ctx dcls
  and trans_dconstrs ctx dconstrs =
    let unbox_cond1 = List.for_all (fun (_, relvs) ->
        List.for_all (fun relv -> relv = N) relvs) dconstrs
    in
    let unbox_cond2 =
      match dconstrs with
      | [ (c, relvs) ] -> List.(length (filter (fun relv -> relv = R) relvs)) = 1
      | _ -> false
    in
    let unbox = unbox_cond1 || unbox_cond2 in
    List.fold_left (fun ctx (c, layout) -> Ctx.(add_constr c { layout; unbox } ctx))
      ctx dconstrs
  in
  aux Ctx.empty dcls
