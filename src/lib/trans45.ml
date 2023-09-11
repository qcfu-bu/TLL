open Names
open Syntax4
open Context45

let fv_expr bound = function
  | Var x when Fv.mem x bound -> Fv.empty
  | Var x -> Fv.singleton x
  | Ctag _ -> Fv.empty
  | Int _ -> Fv.empty
  | Char _ -> Fv.empty
  | String _ -> Fv.empty
  | NULL -> Fv.empty

let rec fv_cmds bound = function
  (* core *)
  | [] -> (Fv.empty, bound)
  | Move (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.union fv1 fv2, bound)
  | Fun { lhs; fn; args; cmds; ret } :: rest ->
    let bound = List.fold_left (fun acc (_, x) ->
        Fv.add x acc)
        (Fv.add fn bound) args
    in
    let fv1, bound = fv_cmds bound cmds in
    let fv2 = fv_expr bound ret in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | App { lhs; fn; args } :: rest ->
    let fv1 = fv_expr bound (Var fn) in
    let fv2 = List.fold_left (fun acc (_, e) ->
        Fv.union acc (fv_expr bound e))
        Fv.empty args
    in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Free e :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds bound rest in
    (Fv.(union fv1 fv2), bound)
  (* inductive *)
  | MkConstr { lhs; fip; args } :: rest ->
    let fv1 =
      match fip with
      | None -> Fv.empty
      | Some e -> fv_expr bound e
    in
    let fv2 = List.fold_left (fun acc e ->
        Fv.union acc (fv_expr bound e))
        Fv.empty args
    in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Match0 { cond; cases } :: rest ->
    let fv1 = fv_expr bound cond in
    let fv2, bound = fv_cases bound cases in 
    let fv3, bound = fv_cmds bound rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Match1 { cond; sort; cases } :: rest ->
    let fv1 = fv_expr bound cond in
    let fv2, bound = fv_cases bound cases in 
    let fv3, bound = fv_cmds bound rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Absurd :: rest -> fv_cmds bound rest
  (* lazy *)
  | Lazy { lhs; cmds; ret } :: rest ->
    let fv1, bound = fv_cmds bound cmds in
    let fv2 = fv_expr bound ret in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Force (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  (* primitive operators *)
  | Neg (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Add (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Sub (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Mul (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Div (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Mod (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Lte (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Gte (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Lt (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Gt (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Eq (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Chr (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Ord (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Push (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Cat (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Size (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Indx (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  (* primitive effects *)
  | Print (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Prerr (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | ReadLn (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Fork (lhs, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Send (lhs, e1, e2) :: rest ->
    let fv1 = fv_expr bound e1 in
    let fv2 = fv_expr bound e2 in
    let fv3, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union (union fv1 fv2) fv3), bound)
  | Recv (lhs, _, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  | Close (lhs, _, e) :: rest ->
    let fv1 = fv_expr bound e in
    let fv2, bound = fv_cmds (Fv.add lhs bound) rest in
    (Fv.(union fv1 fv2), bound)
  (* magic *)
  | Magic :: rest -> fv_cmds bound rest

and fv_cases bound cases =
  List.fold_left (fun (acc, bound) { ctag; args; rhs } ->
      let bound = List.fold_left (fun acc x -> Fv.add x acc) bound args in
      let fv, bound = fv_cmds bound rhs in
      (Fv.union acc fv, bound))
    (Fv.empty, bound) cases

let trans_expr = function
  | Var x -> Syntax5.Var x
  | Ctag c -> Syntax5.Ctag c
  | Int i -> Syntax5.Int i
  | Char c -> Syntax5.Char c
  | String s -> Syntax5.String s
  | NULL -> Syntax5.NULL

let rec trans_cmds (ctx : Ctx.t) lift = function
  (* core *)
  | [] -> ([], lift)
  | Move (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Move (lhs, e) :: rest, lift)
  | Fun { lhs; fn; args; cmds; ret } :: rest ->
    let fname = Name.(mk ("fn" ^ name_of fn)) in
    let xs = List.map snd args in
    let fv1, bound = fv_cmds (Fv.of_list (fn :: xs)) cmds in
    let fv2 = fv_expr bound ret in
    let fvs = Fv.(dump (union fv1 fv2)) in
    let cmds1 = List.mapi (fun i x -> Syntax5.(Env (x, i))) (fn :: fvs) in
    let cmds2, lift = trans_cmds ctx lift cmds in
    let cmds3 = List.mapi (fun i x -> Syntax5.(Setclo (lhs, Var x, i + 1))) fvs in
    let ret = trans_expr ret in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.
      ( MkClo
          { lhs
          ; fn = fname
          ; fvc = List.length fvs
          ; argc = List.length args
          }
        :: cmds3 @ rest
      , DefFun1
          { fn = fname
          ; cmds = cmds1 @ cmds2; ret
          }
        :: lift )
  | App { lhs; fn; args } :: rest ->
    let rest, lift = trans_cmds ctx lift rest in
    (match Ctx.find_opt fn ctx with
     | Some argc ->
       let args = List.map (fun (_, e) -> trans_expr e) args in
       Syntax5.(AppF { lhs; fn; args } :: rest, lift)
     | None ->
       let rhs, _, cmds = List.fold_left (fun (lhs, fn, acc) (s, arg) ->
           let arg = trans_expr arg in
           match s with
           | U -> Syntax5.(Name.mk "x", lhs, AppC { lhs; fn; arg } :: acc)
           | L -> Syntax5.(Name.mk "x", lhs, Free (Var fn) :: AppC { lhs; fn; arg } :: acc))
           (Name.mk "x", fn, []) args
       in
       Syntax5.(List.rev cmds @ [ Move (lhs, Var rhs) ] @ rest, lift))
  | Free e :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Free e :: rest, lift)
  (* inductive *)
  | MkConstr { lhs; fip; ctag; args } :: rest -> _



  | _ -> _
