open Fmt
open Bindlib
open Names
open Syntax2
open Syntax3

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
    try (procs, [], local_var x local) with
    | _ -> (procs, [], Env (env_var x env)))
  | Const x -> (
    try (procs, [], local_const x local) with
    | _ -> (procs, [], Env (env_const x env)))
  | Lam bnd ->
    let x, m = unbind bnd in
    let arg = V.to_string x in
    let procs, instr, ret =
      trans_tm procs [ Local0 (x, Reg arg) ] (Empty :: extend_env local env) m
    in
    let fname = V.(to_string (mk "lambda_fun")) in
    let lhs = V.(to_string (mk "lambda_lhs")) in
    let proc = { fname; arg = Some arg; body = instr; return = ret } in
    ( proc :: procs
    , [ Clo
          { lhs
          ; fname
          ; env_size = List.length env
          ; env_ext = env_of_local local
          }
      ]
    , Reg lhs )
  | App (s, m, n) ->
    let procs, m_instr, m_ret = trans_tm procs local env m in
    let procs, n_instr, n_ret = trans_tm procs local env n in
    let lhs = V.(to_string (mk "app_lhs")) in
    let app_instr =
      match s with
      | U -> [ Call { lhs; fptr = m_ret; aptr = n_ret } ]
      | L -> [ Call { lhs; fptr = m_ret; aptr = n_ret }; FreeClo m_ret ]
    in
    (procs, m_instr @ n_instr @ app_instr, Reg lhs)
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let lhs = V.to_string x in
    let procs, m_instr, m_ret = trans_tm procs local env m in
    let procs, n_instr, n_ret =
      trans_tm procs (Local0 (x, Reg lhs) :: local) env n
    in
    (procs, m_instr @ [ Mov { lhs; rhs = m_ret } ] @ n_instr, n_ret)
  (* data *)
  | Pair (m, n) ->
    let procs, m_instr, m_ret = trans_tm procs local env m in
    let procs, n_instr, n_ret = trans_tm procs local env n in
    let lhs = V.(to_string (mk "pair_lhs")) in
    ( procs
    , m_instr @ n_instr
      @ [ Struct { lhs; ctag = 0; size = 2; data = [ m_ret; n_ret ] } ]
    , Reg lhs )
  | Cons (c, ms) ->
    let procs, ms_instr, ms_ret =
      List.fold_left
        (fun (procs, ms_instr, ms_ret) m ->
          let procs, m_instr, m_ret = trans_tm procs local env m in
          (procs, ms_instr @ m_instr, ms_ret @ [ m_ret ]))
        (procs, [], []) ms
    in
    let lhs = V.(to_string (mk (C.to_string c))) in
    ( procs
    , ms_instr
      @ [ Struct
            { lhs; ctag = C.get_id c; size = List.length ms; data = ms_ret }
        ]
    , Reg lhs )
  | Match (s, m, cls) ->
    let procs, m_instr, m_ret = trans_tm procs local env m in
    let ret = V.(to_string (mk "match_ret")) in
    let procs, cls =
      List.fold_left
        (fun (procs, cls) cl ->
          let procs, cl = trans_cl procs local env ret m_ret cl s in
          (procs, cls @ [ cl ]))
        (procs, []) cls
    in
    (procs, m_instr @ [ Switch { cond = m_ret; cases = cls } ], Reg ret)
  (* monadic *)
  | Return m ->
    let procs, instr, v = trans_tm procs [] (Empty :: extend_env local env) m in
    let fname = V.(to_string (mk "thunk_fun")) in
    let arg = V.(to_string (mk "_")) in
    let lhs = V.(to_string (mk "thunk_lhs")) in
    let proc = { fname; arg = Some arg; body = instr; return = v } in
    ( procs @ [ proc ]
    , [ Clo
          { lhs
          ; fname
          ; env_size = List.length env
          ; env_ext = env_of_local local
          }
      ]
    , Reg lhs )
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let lhs = V.to_string x in
    let procs, m_instr, m_ret = trans_tm procs local env m in
    let procs, n_instr, n_ret =
      trans_tm procs (Local0 (x, Reg lhs) :: local) env n
    in
    ( procs
    , m_instr
      @ [ Call { lhs; fptr = m_ret; aptr = NULL }; FreeClo m_ret ]
      @ n_instr
    , n_ret )
  (* session *)
  | Open prim ->
    let lhs = V.(to_string (mk "open_lhs")) in
    (procs, [ Open { lhs; obj = trans_prim prim } ], Reg lhs)
  | Fork bnd ->
    let x, m = unbind bnd in
    let procs, instr, rhs =
      trans_tm procs [] (Env0 x :: extend_env local env) m
    in
    let lhs = V.(to_string (mk "fork_lhs")) in
    let ret = V.(to_string (mk "fork_ret")) in
    let instr = instr @ [ Mov { lhs = ret; rhs }; FreeThread ] in
    let fname = V.(to_string (mk "fork_fun")) in
    let proc = { fname; arg = None; body = instr; return = Reg ret } in
    ( procs @ [ proc ]
    , instr
      @ [ Open
            { lhs
            ; obj =
                Ch
                  { fname
                  ; env_size = List.length env
                  ; env_ext = env_of_local local
                  }
            }
        ]
    , Reg lhs )
  | Send (rel, m) -> (
    let procs, instr, ret = trans_tm procs local env m in
    let lhs = V.(to_string (mk "send_lhs")) in
    match rel with
    | R -> (procs, instr @ [ Send { lhs; ch = ret; mode = 1 } ], Reg lhs)
    | N -> (procs, instr @ [ Send { lhs; ch = ret; mode = 0 } ], Reg lhs))
  | Recv (rel, m) -> (
    let procs, instr, ret = trans_tm procs local env m in
    let lhs = V.(to_string (mk "recv_lhs")) in
    match rel with
    | R -> (procs, instr @ [ Recv { lhs; ch = ret; mode = 1 } ], Reg lhs)
    | N -> (procs, instr @ [ Recv { lhs; ch = ret; mode = 0 } ], Reg lhs))
  | Close (rol, m) -> (
    let procs, instr, ret = trans_tm procs local env m in
    let lhs = V.(to_string (mk "close_lhs")) in
    match rol with
    | Pos -> (procs, instr @ [ Close { lhs; ch = ret; mode = 1 } ], Reg lhs)
    | Neg -> (procs, instr @ [ Close { lhs; ch = ret; mode = 0 } ], Reg lhs))
  | NULL -> (procs, [], NULL)

and trans_cl procs local env ret m_ret cl s =
  match cl with
  | PPair bnd ->
    let xs, rhs = unmbind bnd in
    let _, cl_instr, local =
      Array.fold_left
        (fun (i, instr, local) x ->
          let lhs = V.to_string x in
          ( i + 1
          , instr @ [ Mov { lhs; rhs = Idx (m_ret, i) } ]
          , local @ [ Local0 (x, Reg lhs) ] ))
        (0, [], local) xs
    in
    let procs, rhs_instr, rhs_ret = trans_tm procs local env rhs in
    let rhs_instr = rhs_instr @ [ Mov { lhs = ret; rhs = rhs_ret }; Break ] in
    let instr =
      match s with
      | U -> cl_instr @ rhs_instr
      | L -> cl_instr @ [ FreeStruct m_ret ] @ rhs_instr
    in
    (procs, (0, instr))
  | PCons (c, bnd) ->
    let xs, rhs = unmbind bnd in
    let _, cl_instr, local =
      Array.fold_left
        (fun (i, instr, local) x ->
          let lhs = V.to_string x in
          ( i + 1
          , instr @ [ Mov { lhs; rhs = Idx (m_ret, i) } ]
          , local @ [ Local0 (x, Reg lhs) ] ))
        (0, [], local) xs
    in
    let procs, rhs_instr, rhs_ret = trans_tm procs local env rhs in
    let rhs_instr = rhs_instr @ [ Mov { lhs = ret; rhs = rhs_ret }; Break ] in
    let instr =
      match s with
      | U -> cl_instr @ rhs_instr
      | L -> cl_instr @ [ FreeStruct m_ret ] @ rhs_instr
    in
    (procs, (C.get_id c, instr))

let trans_dcls res dcls =
  let rec aux procs local env = function
    | [] -> (procs, [], NULL)
    | DMain m :: _ ->
      let lhs = V.(to_string (mk "_")) in
      let procs, instr, ret = trans_tm procs local env m in
      ( procs
      , instr @ [ Call { lhs; fptr = ret; aptr = NULL }; FreeClo ret ]
      , NULL )
    | DTm (x, Lam bnd) :: dcls ->
      let y, m = unbind bnd in
      let xid = I.to_string x in
      let arg = V.to_string y in
      let procs, m_instr, m_ret =
        trans_tm procs
          [ Local0 (y, Reg arg) ]
          (Env1 x :: extend_env local env)
          m
      in
      let fname = V.(to_string (mk "lambda_fun")) in
      let proc = { fname; arg = Some arg; body = m_instr; return = m_ret } in
      let procs, instr, ret =
        aux procs (Local1 (x, Reg xid) :: local) env dcls
      in
      ( proc :: procs
      , Clo
          { lhs = xid
          ; fname
          ; env_size = List.length env
          ; env_ext = env_of_local local
          }
        :: instr
      , ret )
    | DTm (x, m) :: dcls ->
      let xid = I.to_string x in
      let procs, m_instr, m_ret =
        trans_tm procs (Local1 (x, Reg xid) :: local) env m
      in
      let procs, instr, ret =
        aux procs (Local1 (x, Reg xid) :: local) env dcls
      in
      (procs, m_instr @ [ Mov { lhs = xid; rhs = m_ret } ] @ instr, ret)
    | DData (_, _) :: dcls -> aux procs local env dcls
  in
  aux [] [] [] dcls
