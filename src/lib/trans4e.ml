open Fmt
open Names
open Syntax4
open Context4e
open Pprint4

let rec trans_cmds mem cmds = 
  Debug.exec (fun () ->
      try pr "trans_cmds(%a)@." pp_cmd (List.hd cmds)
      with _ -> ());
  match cmds with
  (* end of scope *)
  | [] ->
    let ms, mem = Mem.dump_scope mem in
    let cmds = List.map (fun m -> Free m) ms in
    (cmds, mem)
  (* core *)
  | Move (lhs, m) :: rest -> 
    let rest, mem = trans_cmds mem rest in
    (Move (lhs, m) :: rest, mem)
  | Fun { lhs; fn; args; cmds; ret } :: rest ->
    if List.for_all (fun (s, _) -> s = L) args then
      let cmds, mem = trans_cmds (Mem.new_scope mem) cmds in
      let rest, mem = trans_cmds mem rest in
      (Fun { lhs; fn; args; cmds; ret } :: rest, mem)
    else
      let cmds, _ = trans_cmds Mem.(new_scope empty) cmds in
      let rest, mem = trans_cmds mem rest in
      (Fun { lhs; fn; args; cmds; ret } :: rest, mem)
  | App { lhs; fn; args } :: rest -> 
    let rest, mem = trans_cmds mem rest in
    (App { lhs; fn; args } :: rest, mem)
  | Free m :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Free m :: rest, mem)
  (* inductive *)
  | MkConstr { lhs; fip; ctag; args } :: rest ->
    let size = List.length args in
    (match Mem.pop_stack size mem with
     | Some (m, mem) ->
       let rest, mem = trans_cmds mem rest in
       (MkConstr { lhs; fip = Some m; ctag; args } :: rest, mem)
     | None -> 
       let rest, mem = trans_cmds mem rest in
       (MkConstr { lhs; fip; ctag; args } :: rest, mem))
  | Match0 { cond; cases } :: rest ->
    let cases, mem = trans_match0 mem cases in
    let rest, mem = trans_cmds mem rest in
    (Match0 { cond; cases } :: rest, mem)
  | Match1 { cond; sort; cases } :: rest ->
    let e = Entry.mk cond in
    let cases, mem = trans_match1 mem cases e sort in
    let rest, mem = trans_cmds mem rest in
    (Match1 { cond; sort; cases } :: rest, mem)
  | Absurd :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Absurd :: rest, mem)
  (* lazy *)
  | Lazy { lhs; cmds; ret } :: rest ->
    let cmds, mem = trans_cmds (Mem.new_scope mem) cmds in
    let rest, mem = trans_cmds mem rest in
    (Lazy { lhs; cmds; ret } :: rest, mem)
  | Force (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Force (lhs, m) :: rest, mem)
  (* primitive operators *)
  | Neg (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Neg (lhs, m) :: rest, mem)
  | Add (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Add (lhs, m, n) :: rest, mem)
  | Sub (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Sub (lhs, m, n) :: rest, mem)
  | Mul (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Mul (lhs, m, n) :: rest, mem)
  | Div (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Div (lhs, m, n) :: rest, mem)
  | Mod (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Mod (lhs, m, n) :: rest, mem)
  | Lte (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Lte (lhs, m, n) :: rest, mem)
  | Gte (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Gte (lhs, m, n) :: rest, mem)
  | Lt (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Lt (lhs, m, n) :: rest, mem)
  | Gt (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Gt (lhs, m, n) :: rest, mem)
  | Eq (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Eq (lhs, m, n) :: rest, mem)
  | Chr (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Chr (lhs, m) :: rest, mem)
  | Ord (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Ord (lhs, m) :: rest, mem)
  | Push (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Push (lhs, m, n) :: rest, mem)
  | Cat (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Cat (lhs, m, n) :: rest, mem)
  | Size (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Size (lhs, m) :: rest, mem)
  | Indx (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Indx (lhs, m, n) :: rest, mem)
  (* primitive effects *)
  | Print (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Print (lhs, m) :: rest, mem)
  | Prerr (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Prerr (lhs, m) :: rest, mem)
  | ReadLn (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (ReadLn (lhs, m) :: rest, mem)
  | Fork (lhs, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Fork (lhs, m) :: rest, mem)
  | Send (lhs, m, n) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Send (lhs, m, n) :: rest, mem)
  | Recv (lhs, s, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Recv (lhs, s, m) :: rest, mem)
  | Close (lhs, role, m) :: rest ->
    let rest, mem = trans_cmds mem rest in
    (Close (lhs, role, m) :: rest, mem)
  | Magic :: rest -> 
    let rest, mem = trans_cmds mem rest in
    (Magic :: rest, mem)

and trans_match0 mem cases = 
  let cases, mems =
    cases
    |> List.map (fun { ctag; args; rhs } ->
        let rhs, mem = trans_cmds (Mem.new_scope mem) rhs in
        ({ ctag; args; rhs }, mem))
    |> List.split
  in
  (cases, Mem.union mems)

and trans_match1 mem cases e sort =
  match sort with
  | U -> trans_match0 mem cases
  | L ->
    let cases, mems =
      cases
      |> List.map (fun { ctag; args; rhs } ->
          let mem = Mem.new_scope mem in
          let mem = Mem.push_stack (List.length args) e mem in
          let rhs, mem = trans_cmds mem rhs in
          ({ ctag; args; rhs }, mem))
      |> List.split
    in
    (cases, Mem.union mems)

let trans_dcls dcls =
  let rec aux mem = function
    | [] -> ([], mem)
    | Main { cmds; ret } :: _ ->
      let cmds, mem = trans_cmds mem cmds in
      (Main { cmds; ret } :: dcls, mem)
    | DefFun { fn; args; cmds; ret } :: dcls ->
      if List.for_all (fun (s, _) -> s = L) args then
        let cmds, mem = trans_cmds (Mem.new_scope mem) cmds in
        let dcls, mem = aux mem dcls in
        (DefFun { fn; args; cmds; ret } :: dcls, mem)
      else
        let cmds, mem = trans_cmds Mem.(new_scope empty) cmds in
        let dcls, mem = aux mem dcls in
        (DefFun { fn; args; cmds; ret } :: dcls, mem)
    | DefVal { lhs; cmds; ret } :: dcls ->
      let cmds, mem = trans_cmds mem cmds in
      let dcls, mem = aux mem dcls in
      (DefVal { lhs; cmds; ret } :: dcls, mem)
  in
  fst (aux Mem.empty dcls)
