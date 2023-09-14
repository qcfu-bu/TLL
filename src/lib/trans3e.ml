open Fmt
open Bindlib
open Names
open Syntax3

let var_count bnd = 
  let x0, m = unbind bnd in
  let rec aux = function
    (* core *)
    | Var x -> if eq_vars x x0 then 1 else 0
    | Const _ -> 0
    | Fun bnd -> aux (snd (unbind bnd))
    | Lam (_, bnd) -> aux (snd (unbind bnd))
    | App (_, m, n) -> aux m + aux n
    | Let (m, bnd) -> aux m + aux (snd (unbind bnd))
    (* inductive *)
    | Constr0 _ -> 0
    | Constr1 (_, ms) ->
      List.fold_left (fun acc m -> acc + aux m) 0 ms
    | Match0 (m, cls) ->
      aux m + List.fold_left (fun acc (_, rhs) -> acc + aux rhs) 0 cls
    | Match1 (_, m, cls) ->
      aux m + List.fold_left (fun acc (_, bnd) ->
          let _, rhs = unmbind bnd in
          acc + aux rhs)
        0 cls
    | Absurd -> 0
    (* lazy *)
    | Lazy m -> aux m
    | Force m -> aux m
    (* primitive terms *)
    | Int _ -> 0
    | Char _ -> 0
    | String _ -> 0
    (* primitive operators *)
    | Neg m -> aux m
    | Add (m, n) -> aux m + aux n
    | Sub (m, n) -> aux m + aux n
    | Mul (m, n) -> aux m + aux n
    | Div (m, n) -> aux m + aux n
    | Mod (m, n) -> aux m + aux n
    | Lte (m, n) -> aux m + aux n
    | Gte (m, n) -> aux m + aux n
    | Lt (m, n) -> aux m + aux n
    | Gt (m, n) -> aux m + aux n
    | Eq (m, n) -> aux m + aux n
    | Chr m -> aux m
    | Ord m -> aux m
    | Push (m, n) -> aux m + aux n
    | Cat (m, n) -> aux m + aux n
    | Size m -> aux m
    | Indx (m, n) -> aux m + aux n
    (* primitive effects *)
    | Print m -> aux m
    | Prerr m -> aux m
    | ReadLn m -> aux m
    | Fork m -> aux m
    | Send (m, n) -> aux m + aux n
    | Recv (_, m) -> aux m
    | Close (_, m) -> aux m
    (* erasure *)
    | NULL -> 0
    (* magic *)
    | Magic -> 0
  in
  aux m

let rec simpl_arg = function
  | Var _ -> true
  | Const _ -> true
  | Int _ -> true
  | Char _ -> true
  | String _ -> true
  | Constr0 _ -> true
  | Constr1 (_, ms) -> List.for_all simpl_arg ms
  | Absurd -> true
  | NULL -> true
  | Magic -> true
  | _ -> false

let rec trans_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Fun bnd when binder_occur bnd ->
    let x, m = unbind bnd in
    _Fun (bind_var x (trans_tm m))
  | Fun bnd -> trans_tm (snd (unbind bnd))
  | Lam (s, bnd) ->
    let x, m = unbind bnd in
    _Lam s (bind_var x (trans_tm m))
  | App (s, m, n) ->
    let _m = trans_tm m in
    let _n = trans_tm n in
    (match unbox _m, unbox _n with
     | Lam (s, bnd), n when simpl_arg n -> trans_tm (subst bnd n)
     | Lam (s, bnd), n when var_count bnd <= 1 -> trans_tm (subst bnd n)
     | Lam (s, bnd), n -> _Let _n (box_binder lift_tm bnd)
     | _, _ -> _App s _m _n)
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let _m = trans_tm m in
    let _bnd = bind_var x (trans_tm n) in
    (match unbox _m with
     | Var x -> lift_tm (subst (unbox _bnd) (Var x))
     | _ -> _Let _m _bnd)
  (* inductive *)
  | Constr0 c -> _Constr0 c
  | Constr1 (c, ms) -> 
    let ms = List.map trans_tm ms in
    _Constr1 c (box_list ms)
  | Match0 (m, cls) ->
    let m = trans_tm m in
    let cls = List.map (fun (c, rhs) ->
        let rhs = trans_tm rhs in _PConstr c rhs)
        cls
    in
    _Match0 m (box_list cls)
  | Match1 (s, m, cls) ->
    let m = trans_tm m in
    let cls = List.map (fun (c, bnd) ->
        let xs, rhs = unmbind bnd in
        let rhs = trans_tm rhs in
        _PConstr c (bind_mvar xs rhs))
        cls
    in
    _Match1 s m (box_list cls)
  | Absurd -> _Absurd
  (* lazy *)
  | Lazy m -> _Lazy (trans_tm m)
  | Force m ->
    let m = trans_tm m in
    (match unbox m with
     | Lazy m -> lift_tm m
     | Let (m, bnd) ->
       let x, n = unbind bnd in
       let n = trans_tm (Force n) in
       _Let (lift_tm m) (bind_var x n)
     | Match0 (m, cls) -> 
       let cls = List.map (fun (c, rhs) ->
           _PConstr c (trans_tm (Force rhs)))
           cls
       in
       _Match0 (lift_tm m) (box_list cls)
     | Match1 (s, m, cls) -> 
       let cls = List.map (fun (c, bnd) ->
           let xs, rhs = unmbind bnd in
           _PConstr c (bind_mvar xs (trans_tm (Force rhs))))
           cls
       in
       _Match1 s (lift_tm m) (box_list cls)
     | _ -> _Force m)
  (* primitive terms *)
  | Int i -> _Int i
  | Char c -> _Char c
  | String s -> _String s
  (* primitive operators *)
  | Neg m -> _Neg (trans_tm m)
  | Add (m, n) -> _Add (trans_tm m) (trans_tm n)
  | Sub (m, n) -> _Sub (trans_tm m) (trans_tm n)
  | Mul (m, n) -> _Mul (trans_tm m) (trans_tm n)
  | Div (m, n) -> _Div (trans_tm m) (trans_tm n)
  | Mod (m, n) -> _Mod (trans_tm m) (trans_tm n)
  | Lte (m, n) -> _Lte (trans_tm m) (trans_tm n)
  | Gte (m, n) -> _Gte (trans_tm m) (trans_tm n)
  | Lt (m, n) -> _Lt (trans_tm m) (trans_tm n)
  | Gt (m, n) -> _Gt (trans_tm m) (trans_tm n)
  | Eq (m, n) -> _Eq (trans_tm m) (trans_tm n)
  | Chr m -> _Chr (trans_tm m)
  | Ord m -> _Ord (trans_tm m)
  | Push (m, n) -> _Push (trans_tm m) (trans_tm n)
  | Cat (m, n) -> _Cat (trans_tm m) (trans_tm n)
  | Size m -> _Size (trans_tm m)
  | Indx (m, n) -> _Indx (trans_tm m) (trans_tm n)
  (* primitive effects *)
  | Print m -> _Print (trans_tm m)
  | Prerr m -> _Prerr (trans_tm m)
  | ReadLn m -> _ReadLn (trans_tm m)
  | Fork m -> _Fork (trans_tm m)
  | Send (m, n) -> _Send (trans_tm m) (trans_tm n)
  | Recv (s, m) -> (_Recv s) (trans_tm m)
  | Close (role, m) -> (_Close role) (trans_tm m)
  (* erasure *)
  | NULL -> _NULL
  (* magic *)
  | Magic -> _Magic

let trans_dcls dcls = 
  let rec aux = function
    | [] -> []
    | Main { body } :: [] -> Main { body = unbox (trans_tm body) } :: []
    | Main _ :: _ -> failwith "trans12.trans_dcls(Main)"
    | Definition { name; body } :: dcls ->
      let body_elab = trans_tm body in
      let dcls_elab = aux dcls in
      Definition { name; body = unbox body_elab } :: dcls_elab
  in
  let dcls = aux dcls in
  pf Debug.fmt "%a" Pprint3.pp_dcls dcls;
  pf Debug.fmt "@.@.[trans3e success]";
  pf Debug.fmt "@.@.-----------------------------------------@.@.";
  dcls