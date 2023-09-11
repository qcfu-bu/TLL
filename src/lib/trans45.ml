open Names
open Syntax4
open Context45

let fv_expr ctx = function
  | Var x when Ctx.mem x ctx -> Ctx.empty
  | Var x -> Ctx.singleton x
  | Ctag _ -> Ctx.empty
  | Int _ -> Ctx.empty
  | Char _ -> Ctx.empty
  | String _ -> Ctx.empty
  | NULL -> Ctx.empty

let rec fv_cmds ctx = function
  (* core *)
  | [] -> (Ctx.empty, ctx)
  | Move (lhs, e) :: rest ->
    let fv1 = fv_expr ctx e in
    let fv2, ctx = fv_cmds (Ctx.add lhs ctx) rest in
    (Ctx.union fv1 fv2, ctx)
  | Fun { lhs; fn; args; cmds; ret } :: rest ->
    let ctx1 = List.fold_left (fun acc (_, x) ->
        Ctx.add x acc)
        (Ctx.add fn ctx) args
    in
    let fv1, ctx1 = fv_cmds ctx1 cmds in
    let fv2 = fv_expr ctx1 ret in
    let fv3, ctx = fv_cmds (Ctx.add lhs ctx) rest in
    (Ctx.(union (union fv1 fv2) fv3), ctx)
  | App { lhs; fn; args } :: rest ->
    let fv1 = fv_expr ctx fn in
    let fv2 = List.fold_left (fun acc (_, e) ->
        Ctx.union acc (fv_expr ctx e))
        Ctx.empty args
    in
    let fv3, ctx = fv_cmds (Ctx.add lhs ctx) rest in
    (Ctx.(union (union fv1 fv2) fv3), ctx)
  | Free e :: rest ->
    let fv1 = fv_expr ctx e in
    let fv2, ctx = fv_cmds ctx rest in
    (Ctx.(union fv1 fv2), ctx)
  (* inductive *)
  | MkConstr { lhs; fip; args } :: rest ->
    let fv1 =
      match fip with
      | None -> Ctx.empty
      | Some e -> fv_expr ctx e
    in
    let fv2 = List.fold_left (fun acc e ->
        Ctx.union acc (fv_expr ctx e))
        Ctx.empty args
    in
    let fv3, ctx = fv_cmds (Ctx.add lhs ctx) rest in
    (Ctx.(union (union fv1 fv2) fv3), ctx)
  | Match0 { cond; cases } :: rest ->
    let fv1 = fv_expr ctx cond in
    let fv2, ctx = fv_cases ctx cases in 
    let fv3, ctx = fv_cmds ctx rest in
    (Ctx.(union (union fv1 fv2) fv3), ctx)
  | Match1 { cond; sort; cases } :: rest ->
    let fv1 = fv_expr ctx cond in
    let fv2, ctx = fv_cases ctx cases in 
    let fv3, ctx = fv_cmds ctx rest in
    (Ctx.(union (union fv1 fv2) fv3), ctx)
  | Absurd :: rest -> fv_cmds ctx rest
  (* lazy *)
  | Lazy { lhs; cmds; ret } :: rest ->
    let fv1, ctx1 = fv_cmds ctx cmds in
    let fv2 = fv_expr ctx1 ret in
    let fv3, ctx = fv_cmds (Ctx.add lhs ctx) rest in
    (Ctx.(union (union fv1 fv2) fv3), ctx)

  | _ -> _

and fv_cases ctx cases =
  List.fold_left (fun (acc, ctx) { ctag; args; rhs } ->
      let ctx = List.fold_left (fun acc x -> Ctx.add x acc) ctx args in
      let fv, ctx = fv_cmds ctx rhs in
      (Ctx.union acc fv, ctx))
    (Ctx.empty, ctx) cases
