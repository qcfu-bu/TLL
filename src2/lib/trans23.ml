open Fmt
open Bindlib
open Names
open Syntax2
open Syntax3

type 'a trans23 = toplevel * Trans12.Resolver.t -> 'a * toplevel

type local_entry =
  | Local0 of V.t * value
  | Local1 of I.t * value

type env_entry =
  | Empty
  | Env0 of V.t
  | Env1 of I.t

let rec local_var y = function
  | [] -> failwith "local_var(%a)" V.pp y
  | Local0 (x, v) :: xs ->
    if eq_vars x y then
      v
    else
      local_var y xs
  | _ :: xs -> local_var y xs

let rec local_const y = function
  | [] -> failwith "local_const(%a)" I.pp y
  | Local1 (x, v) :: xs ->
    if I.equal x y then
      v
    else
      local_const y xs
  | _ :: xs -> local_const y xs

let env_var y env =
  let rec loop i = function
    | [] -> failwith "env_var(%a)" V.pp y
    | Env0 x :: xs ->
      if eq_vars x y then
        i
      else
        loop (i + 1) xs
    | _ :: xs -> loop (i + 1) xs
  in
  loop 0 env

let env_const y env =
  let rec loop i = function
    | [] -> failwith "env_const(%a)" I.pp y
    | Env1 x :: xs ->
      if I.equal x y then
        i
      else
        loop (i + 1) xs
    | _ :: xs -> loop (i + 1) xs
  in
  loop 0 env

let rec extend_env local env =
  List.map
    (function
      | Local0 (x, _) -> Env0 x
      | Local1 (x, _) -> Env1 x)
    local
  @ env

let env_of_local local =
  List.map
    (function
      | Local0 (_, v) -> v
      | Local1 (_, v) -> v)
    local

let trans_prim = function
  | Syntax2.Stdin -> Syntax3.Stdin
  | Syntax2.Stdout -> Syntax3.Stdout
  | Syntax2.Stderr -> Syntax3.Stderr

let rec trans_tm procs local env m =
  match m with
  (* core *)
  | Var x -> (
    try ([], [], local_var x local) with
    | _ -> Syntax3.([], [], Env (env_var x env)))
  | Const x -> Syntax3.([], [], Env (env_const x env))
  | Lam bnd ->
    let x, m = unbind bnd in
    let arg = V.to_string x in
    let procs, instr, v =
      trans_tm procs [ Local0 (x, Reg arg) ] (Empty :: extend_env local env) m
    in
    let name = V.(to_string (mk "lam")) in
    let tmp = V.(to_string (mk "clo")) in
    let proc = { name; arg = Some arg; body = instr; return = v } in
    ( procs @ [ proc ]
    , [ MakeClo (tmp, name, List.length env, env_of_local local) ]
    , Reg tmp )
  | App (s, m, n) ->
    let procs, m_instr, m_v = trans_tm procs local env m in
    let procs, n_instr, n_v = trans_tm procs local env n in
    let tmp = V.(to_string (mk "app")) in
    let app_instr =
      match s with
      | U -> [ CallClo (tmp, m_v, n_v) ]
      | L -> [ CallClo (tmp, m_v, n_v); FreeClo m_v ]
    in
    (procs, m_instr @ n_instr @ app_instr, Reg tmp)
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let id = V.to_string x in
    let procs, m_instr, m_v = trans_tm procs local env m in
    let procs, n_instr, n_v =
      trans_tm procs (Local0 (x, Reg id) :: local) env n
    in
    (procs, m_instr @ [ Mov (id, m_v) ] @ n_instr, n_v)
  (* data *)
  | Pair (m, n) ->
    let procs, m_instr, m_v = trans_tm procs local env m in
    let procs, n_instr, n_v = trans_tm procs local env n in
    let tmp = V.(to_string (mk "pair")) in
    (procs, m_instr @ n_instr @ [ MakeStruct (tmp, 0, [ m_v; n_v ]) ], Reg tmp)
  | Cons (c, ms) ->
    let procs, ms_instr, ms_v =
      List.fold_left
        (fun (procs, ms_instr, ms_v) m ->
          let proc, m_instr, m_v = trans_tm procs local env m in
          (procs, ms_instr @ m_instr, ms_v @ [ m_v ]))
        (procs, [], []) ms
    in
    let tmp = V.(to_string (mk (C.to_string c))) in
    (procs, ms_instr @ [ MakeStruct (tmp, C.get_id c, ms_v) ], Reg tmp)
  | Match (s, m, cls) ->
    let procs, m_instr, m_v = trans_tm procs local env m in
    let tmp = V.(to_string (mk "match")) in
    let procs, cls =
      List.fold_left
        (fun (procs, cls) cl ->
          let procs, cl = trans_cl procs local env tmp m_v cl s in
          (procs, cls @ [ cl ]))
        (procs, []) cls
    in
    (procs, m_instr @ [ Switch (m_v, cls) ], Reg tmp)
  (* monadic *)
  | Return m ->
    let procs, instr, v = trans_tm procs [] (Empty :: extend_env local env) m in
    let name = V.(to_string (mk "return")) in
    let arg = V.(to_string (mk "_")) in
    let tmp = V.(to_string (mk "tmp")) in
    let proc = { name; arg = Some arg; body = instr; return = v } in
    ( procs @ [ proc ]
    , [ MakeClo (tmp, name, List.length env, env_of_local local) ]
    , Reg tmp )
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let id = V.to_string x in
    let procs, m_instr, m_v = trans_tm procs local env m in
    let procs, n_instr, n_v =
      trans_tm procs (Local0 (x, Reg id) :: local) env n
    in
    (procs, m_instr @ [ CallClo (id, m_v, NULL) ] @ n_instr, n_v)
  (* session *)
  | Open prim ->
    let tmp = V.(to_string (mk "tmp")) in
    (procs, [ Open (tmp, trans_prim prim) ], Reg tmp)
  | Fork bnd ->
    let x, m = unbind bnd in
    let procs, instr, v =
      trans_tm procs [] (Env0 x :: extend_env local env) m
    in
    let ret = V.(to_string (mk "fork_return")) in
    let instr = instr @ [ Mov (ret, v); FreeThread ] in
    let res = V.(to_string (mk "fork_res")) in
    let name = V.(to_string (mk "fork")) in
    let proc = { name; arg = None; body = instr; return = Reg ret } in
    ( procs @ [ proc ]
    , instr @ [ Open (res, Ch (name, v, List.length env, env_of_local local)) ]
    , Reg res )
  | Send (rel, m) -> (
    let procs, instr, v = trans_tm procs local env m in
    match rel with
    | R ->
      let tmp = V.(to_string (mk "send_tmp")) in
      (procs, instr @ [ Send (tmp, v) ], Reg tmp)
    | N -> (procs, instr, v))
  | Recv (rel, m) -> (
    let procs, instr, v = trans_tm procs local env m in
    let tmp = V.(to_string (mk "recv_tmp")) in
    match rel with
    | R -> (procs, instr @ [ Recv (tmp, v) ], Reg tmp)
    | N -> (procs, instr @ [ MakeStruct (tmp, 0, [ NULL; v ]) ], Reg tmp))
  | Close (rol, m) -> (
    let procs, instr, v = trans_tm procs local env m in
    let tmp = V.(to_string (mk "close_tmp")) in
    match rol with
    | Pos -> (procs, instr @ [ Close (tmp, v) ], Reg tmp)
    | Neg ->
      (procs, instr @ [ MakeStruct (tmp, C.get_id Prelude1.tt_c, []) ], Reg tmp)
    )
  | NULL -> (procs, [], NULL)

and trans_cl procs local env tmp v cl s =
  match cl with
  | PPair bnd ->
    let xs, rhs = unmbind bnd in
    let _, cl_instr, local =
      Array.fold_left
        (fun (i, instr, local) x ->
          let id = V.to_string x in
          ( i + 1
          , instr @ [ Mov (id, Proj (v, i)) ]
          , local @ [ Local0 (x, Reg id) ] ))
        (0, [], local) xs
    in
    let procs, rhs_instr, rhs_v = trans_tm procs local env rhs in
    let rhs_instr = rhs_instr @ [ Mov (tmp, rhs_v); Break ] in
    let instr =
      match s with
      | U -> cl_instr @ rhs_instr
      | L -> cl_instr @ [ FreeStruct v ] @ rhs_instr
    in
    (procs, (0, instr))
  | PCons (c, bnd) ->
    let xs, rhs = unmbind bnd in
    let _, cl_instr, local =
      Array.fold_left
        (fun (i, instr, local) x ->
          let id = V.to_string x in
          ( i + 1
          , instr @ [ Mov (id, Proj (v, i)) ]
          , local @ [ Local0 (x, Reg id) ] ))
        (0, [], local) xs
    in
    let procs, rhs_instr, rhs_v = trans_tm procs local env rhs in
    let rhs_instr = rhs_instr @ [ Mov (tmp, rhs_v); Break ] in
    let instr =
      match s with
      | U -> cl_instr @ rhs_instr
      | L -> cl_instr @ [ FreeStruct v ] @ rhs_instr
    in
    (procs, (C.get_id c, instr))
