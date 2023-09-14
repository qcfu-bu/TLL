open Fmt
open Bindlib
open Names
open Syntax3
open Context34
open Pprint3

let trans_sort = function
  | U -> Syntax4.U
  | L -> Syntax4.L

let rec gather_lam = function
  | Lam (s, bnd) ->
    let x, m = unbind bnd in
    let sxs, m = gather_lam m in
    ((s, x) :: sxs, m)
  | m -> ([], m)

let rec trans_tm ctx m = 
  Debug.exec (fun () -> pr "trans34_tm(%a)@." pp_tm m);
  match m with
  (* core *)
  | Var x -> ([], Ctx.find_var x ctx)
  | Const x -> ([], Ctx.find_const x ctx)
  | Fun bnd ->
    let x, m = unbind bnd in
    let sxs, m = gather_lam m in
    let lhs = Syntax4.(Name.mk "x") in
    let fn = Syntax4.(Name.mk (name_of x)) in
    let ctx, args = List.fold_left_map (fun acc (s, x) ->
        let n = Syntax4.(Name.mk (name_of x)) in
        (Ctx.add_var x (Var n) acc, (trans_sort s, n)))
        (Ctx.add_var x (Var fn) ctx) sxs
    in
    let cmds, ret = trans_tm ctx m in
    Syntax4.([ Fun { lhs; fn; args; cmds; ret } ], Var lhs)
  | Lam _ as m ->
    let sxs, m = gather_lam m in
    let lhs = Syntax4.(Name.mk "x") in
    let fn = Syntax4.(Name.mk "lam") in
    let ctx, args = List.fold_left_map (fun acc (s, x) ->
        let n = Syntax4.(Name.mk (name_of x)) in
        (Ctx.add_var x (Var n) acc, (trans_sort s, n)))
        ctx sxs
    in
    let cmds, ret = trans_tm ctx m in
    Syntax4.([ Fun { lhs; fn; args; cmds; ret } ], Var lhs)
  | App _ as m ->
    let lhs = Syntax4.(Name.mk "x") in
    let hd, sp = unApps m in
    let cmds1, fn =
      match trans_tm ctx hd with
      | cmds1, Var fn -> (cmds1, fn)
      | _ -> failwith "trans34(App(%a))" pp_tm m
    in
    let cmds2, args = List.fold_left_map (fun acc (m, s) ->
        let cmds, ret = trans_tm ctx m in
        (acc @ cmds, (trans_sort s, ret)))
        [] sp
    in
    Syntax4.(cmds1 @ cmds2 @ [ App { lhs; fn; args } ], Var lhs) 
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let lhs = Syntax4.(Name.mk (name_of x)) in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm (Ctx.add_var x (Var lhs) ctx) n in
    Syntax4.(cmds1 @ [ Move (lhs, ret1) ] @ cmds2, ret2)
  (* inductive *)
  | Constr0 c -> Syntax4.([], Ctag c)
  | Constr1 (c, ms) ->
    let cmds, args = List.fold_left_map (fun acc m ->
        let cmds, ret = trans_tm ctx m in
        (acc @ cmds, ret))
        [] ms
    in
    let lhs = Name.mk "x" in
    Syntax4.(cmds @ [ MkConstr { lhs; fip = None; ctag = c; args } ], Var lhs)
  | Match0 (m, cls) ->
    let lhs = Name.mk "x" in
    let cmds, cond = trans_tm ctx m in
    let cases = trans_cl0s ctx cls lhs in
    Syntax4.(cmds @ [ Match0 { cond; cases } ], Var lhs)
  | Match1 (s, m, cls) ->
    let lhs = Name.mk "x" in
    let cmds, cond = trans_tm ctx m in
    let cases = trans_cl1s ctx cls lhs in
    Syntax4.(cmds @ [ Match1 { sort = trans_sort s; cond; cases; } ], Var lhs)
  | Absurd -> Syntax4.([ Absurd ], NULL)
  (* lazy *)
  | Lazy m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.([ Lazy { lhs; cmds; ret } ], Var lhs)
  | Force m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Force (lhs, ret) ], Var lhs)
  (* primitive terms *)
  | Int i -> Syntax4.([], Int i)
  | Char c -> Syntax4.([], Char c)
  | String s ->
    let lhs = Name.mk "x" in
    Syntax4.([ Str (lhs, s) ], Var lhs)
  (* primitive operators *)
  | Neg m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Neg (lhs, ret) ], Var lhs)
  | Add (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Add (lhs, ret1, ret2) ], Var lhs)
  | Sub (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Sub (lhs, ret1, ret2) ], Var lhs)
  | Mul (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Mul (lhs, ret1, ret2) ], Var lhs)
  | Div (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Div (lhs, ret1, ret2) ], Var lhs)
  | Mod (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Mod (lhs, ret1, ret2) ], Var lhs)
  | Lte (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Lte (lhs, ret1, ret2) ], Var lhs)
  | Gte (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Gte (lhs, ret1, ret2) ], Var lhs)
  | Lt (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Lt (lhs, ret1, ret2) ], Var lhs)
  | Gt (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Gt (lhs, ret1, ret2) ], Var lhs)
  | Eq (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Eq (lhs, ret1, ret2) ], Var lhs)
  | Chr m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Chr (lhs, ret) ], Var lhs)
  | Ord m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Ord (lhs, ret) ], Var lhs)
  | Push (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Push (lhs, ret1, ret2) ], Var lhs)
  | Cat (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Cat (lhs, ret1, ret2) ], Var lhs)
  | Size m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Size (lhs, ret) ], Var lhs)
  | Indx (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Indx (lhs, ret1, ret2) ], Var lhs)
  (* primitive effects *)
  | Print m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Print (lhs, ret) ], Var lhs)
  | Prerr m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Prerr (lhs, ret) ], Var lhs)
  | ReadLn m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ ReadLn (lhs, ret) ], Var lhs)
  | Fork m ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Fork (lhs, ret) ], Var lhs)
  | Send (m, n) ->
    let lhs = Name.mk "x" in
    let cmds1, ret1 = trans_tm ctx m in
    let cmds2, ret2 = trans_tm ctx n in
    Syntax4.(cmds1 @ cmds2 @ [ Send (lhs, ret1, ret2) ], Var lhs)
  | Recv (s, m) ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Recv (lhs, trans_sort s, ret) ], Var lhs)
  | Close (role, m) ->
    let lhs = Name.mk "x" in
    let cmds, ret = trans_tm ctx m in
    Syntax4.(cmds @ [ Close (lhs, role, ret) ], Var lhs)
  (* erasure *)
  | NULL -> Syntax4.([], NULL)
  | Magic -> Syntax4.([ Magic ], NULL)

and trans_cl0s ctx cls lhs =
  List.map (fun (c, rhs) ->
      let cmds, ret = trans_tm ctx rhs in
      Syntax4.{ ctag = c; args = []; rhs = cmds @ [ Move (lhs, ret) ] })
    cls

and trans_cl1s ctx cls lhs =
  List.map (fun (c, bnd) ->
      let xs, rhs = unmbind bnd in
      let ctx, args = List.fold_left_map (fun ctx x ->
          let n = Syntax4.(Name.mk (name_of x)) in
          (Ctx.add_var x (Var n) ctx, n))
          ctx (Array.to_list xs)
      in
      let cmds, ret = trans_tm ctx rhs in
      Syntax4.{ ctag = c; args; rhs = cmds @ [ Move (lhs, ret) ] })
    cls

let trans_dcls dcls =
  let rec aux ctx dcls = 
    match dcls with
    | [] -> []
    | Main { body } as dcl :: dcls ->
      Debug.exec (fun () -> pr "trans34_dcl(%a)@." pp_dcl dcl);
      let cmds, ret = trans_tm ctx body in
      let dcls = aux ctx dcls in
      Syntax4.(Main { cmds; ret } :: dcls)
    | Definition { name = x; body } as dcl :: dcls ->
      Debug.exec (fun () -> pr "trans34_dcl(%a)@." pp_dcl dcl);
      (match body with
       | Fun bnd ->
         let fn = Syntax4.(Name.mk (Const.name_of x)) in
         let m = subst bnd (Const x) in
         let sxs, m = gather_lam m in
         let ctx1, args = List.fold_left_map (fun acc (s, x) ->
             let n = Syntax4.(Name.mk (name_of x)) in
             (Ctx.add_var x (Var n) acc, (trans_sort s, n)))
             (Ctx.add_const x (Var fn) ctx) sxs
         in
         let cmds, ret = trans_tm ctx1 m in
         let dcls = aux (Ctx.add_const x (Var fn) ctx) dcls in
         Syntax4.(DefFun { fn; args; cmds; ret } :: dcls)
       | Lam _ as m ->
         let fn = Syntax4.(Name.mk (Const.name_of x)) in
         let sxs, m = gather_lam m in
         let ctx1, args = List.fold_left_map (fun acc (s, x) ->
             let n = Syntax4.(Name.mk (name_of x)) in
             (Ctx.add_var x (Var n) acc, (trans_sort s, n)))
             (Ctx.add_const x (Var fn) ctx) sxs
         in
         let cmds, ret = trans_tm ctx1 m in
         let dcls = aux (Ctx.add_const x (Var fn) ctx) dcls in
         Syntax4.(DefFun { fn; args; cmds; ret } :: dcls)
       | _ ->
         let lhs = Syntax4.(Name.mk (Const.name_of x)) in
         let cmds, ret = trans_tm ctx body in
         let dcls = aux (Ctx.add_const x (Var lhs) ctx) dcls in
         Syntax4.(DefVal { lhs; cmds; ret } :: dcls))
  in
  let dcls = aux Ctx.empty dcls in
  pf Debug.fmt "%a" Pprint4.pp_dcls dcls;
  pf Debug.fmt "@.@.[trans34 success]";
  pf Debug.fmt "@.@.-----------------------------------------@.@.";
  dcls
