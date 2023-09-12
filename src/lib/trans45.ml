open Names
open Syntax4
open Context45
open Prelude1

let fv_expr bound = function
  | Var x when Fv.mem x bound -> Fv.empty
  | Var x -> Fv.singleton x
  | Ctag _ -> Fv.empty
  | Int _ -> Fv.empty
  | Char _ -> Fv.empty
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
  | Str (lhs, _) :: rest -> fv_cmds (Fv.add lhs bound) rest 
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
  | NULL -> Syntax5.NULL

let rec trans_cmds (ctx : Ctx.t) lift = function
  (* core *)
  | [] -> ([], lift)
  | Move (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Move1 (lhs, e) :: rest, lift)
  | Fun { lhs; fn; args; cmds; ret } :: rest ->
    let fname = Name.(mk ("fn1_" ^ name_of fn)) in
    let xs = List.map snd args in
    let fv1, bound = fv_cmds (Fv.of_list (fn :: xs)) cmds in
    let fv2 = fv_expr bound ret in
    let fvs = Fv.(dump (union fv1 fv2)) in
    let cmds1 = List.mapi (fun i x -> Syntax5.(Env (x, i))) (fn :: fvs @ xs) in
    let cmds2, lift = trans_cmds ctx lift cmds in
    let cmds3 = List.mapi (fun i x -> Syntax5.(SetClo (lhs, Var x, i + 1))) fvs in
    let ret = trans_expr ret in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.
      ( MkClo1
          { lhs
          ; fn = fname
          ; fvc = List.length fvs
          ; argc = List.length args
          }
        :: cmds3 @ rest
      , DefFun1
          { fn = fname
          ; cmds = cmds1 @ cmds2
          ; ret
          }
        :: lift )
  | App { lhs; fn; args } :: rest ->
    let rest, lift = trans_cmds ctx lift rest in
    (match Ctx.find_opt fn ctx with
     | Some (fn, argc) when argc = List.length args ->
       let args = List.map (fun (_, e) -> trans_expr e) args in
       Syntax5.(AppF { lhs; fn; args } :: rest, lift)
     | _ ->
       let _, rhs, cmds = List.fold_left (fun (lhs, rhs, acc) (s, arg) ->
           let arg = trans_expr arg in
           Syntax5.
             (match s with
              | U -> (Name.mk "x", lhs, AppC { lhs; fn = rhs; arg } :: acc)
              | L -> (Name.mk "x", lhs, Free (Var rhs) :: AppC { lhs; fn = rhs; arg } :: acc)))
           (Name.mk "x", fn, []) args
       in
       Syntax5.(List.rev cmds @ [ Move1 (lhs, Var rhs) ] @ rest, lift))
  | Free e :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Free e :: rest, lift)
  (* inductive *)
  | MkConstr { lhs; fip; ctag; args } :: rest ->
    let cmds = List.mapi (fun i e -> Syntax5.SetBox (lhs, trans_expr e, i)) args in
    let rest, lift = trans_cmds ctx lift rest in
    (match fip with
     | Some e -> Syntax5.(ReBox { lhs; fip = trans_expr e; ctag } :: cmds @ rest, lift)
     | None -> Syntax5.(MkBox { lhs; ctag; argc = List.length args } :: cmds @ rest, lift))
  | Match0 { cond; cases } :: rest ->
    let cond = trans_expr cond in
    let cases, lift = trans_cases ctx lift cond cases in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Switch { cond; cases } :: rest, lift)
  | Match1 { cond; cases } :: rest ->
    let cond = trans_expr cond in
    let cases, lift = trans_cases ctx lift cond cases in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Switch { cond = CtagOf cond; cases } :: rest, lift)
  | Absurd :: rest ->
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Absurd :: rest, lift)
  (* lazy *)
  | Lazy { lhs; cmds; ret } :: rest ->
    let fname = Name.mk "lazy_" in
    let fv1, bound = fv_cmds Fv.empty cmds in
    let fv2 = fv_expr bound ret in
    let fvs = Fv.(dump (union fv1 fv2)) in
    let cmds1 = List.mapi (fun i x -> Syntax5.(Env (x, i))) fvs in
    let cmds2, lift = trans_cmds ctx lift cmds in
    let cmds3 = List.mapi (fun i x -> Syntax5.(SetLazy (lhs, Var x, i))) fvs in
    let ret = trans_expr ret in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.
      ( Lazy
          { lhs
          ; fn = fname
          ; fvc = List.length fvs 
          }
        :: cmds3 @ rest
      , DefFun1 
          { fn = fname
          ; cmds = cmds1 @ cmds2
          ; ret
          }
        :: lift )
  | Force (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Force (lhs, e) :: Free e :: rest, lift)
  (* primitive operators *)
  | Neg (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Neg (lhs, e) :: rest, lift)
  | Add (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Add (lhs, e1, e2) :: rest, lift)
  | Sub (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Sub (lhs, e1, e2) :: rest, lift)
  | Mul (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Mul (lhs, e1, e2) :: rest, lift)
  | Div (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Div (lhs, e1, e2) :: rest, lift)
  | Mod (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Mod (lhs, e1, e2) :: rest, lift)
  | Lte (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Lte (lhs, e1, e2) :: rest, lift)
  | Gte (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Gte (lhs, e1, e2) :: rest, lift)
  | Lt (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Lt (lhs, e1, e2) :: rest, lift)
  | Gt (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Gt (lhs, e1, e2) :: rest, lift)
  | Eq (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Eq (lhs, e1, e2) :: rest, lift)
  | Chr (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Chr (lhs, e) :: rest, lift)
  | Ord (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Ord (lhs, e) :: rest, lift)
  | Str (lhs, s) :: rest ->
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Str (lhs, s) :: rest, lift)
  | Push (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Push (lhs, e1, e2) :: rest, lift)
  | Cat (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Cat (lhs, e1, e2) :: rest, lift)
  | Size (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Size (lhs, e) :: rest, lift)
  | Indx (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Indx (lhs, e1, e2) :: rest, lift)
  (* primitive effects *)
  | Print (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Print (lhs, e) :: rest, lift)
  | Prerr (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Prerr (lhs, e) :: rest, lift)
  | ReadLn (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(ReadLn (lhs, e) :: rest, lift)
  | Fork (lhs, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Fork (lhs, e) :: rest, lift)
  | Send (lhs, e1, e2) :: rest ->
    let e1 = trans_expr e1 in
    let e2 = trans_expr e2 in
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Send (lhs, e1, e2) :: rest, lift)
  | Recv (lhs, s, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    (match s with
     | U -> Syntax5.(Recv0 (lhs, e) :: rest, lift)
     | L -> Syntax5.(Recv1 (lhs, e) :: rest, lift))
  | Close (lhs, role, e) :: rest ->
    let e = trans_expr e in
    let rest, lift = trans_cmds ctx lift rest in
    if role
    then Syntax5.(Close0 (lhs, e) :: rest, lift)
    else Syntax5.(Close1 (lhs, e) :: rest, lift)
  (* magic *)
  | Magic :: rest ->
    let rest, lift = trans_cmds ctx lift rest in
    Syntax5.(Magic :: rest, lift)

and trans_cases ctx lift cond cases =
  let lift, cases = List.fold_left_map (fun lift { ctag; args; rhs } ->
      let cmds1 = List.mapi (fun i x -> Syntax5.(GetBox (x, cond, i))) args in
      let cmds2, lift = trans_cmds ctx lift rhs in
      (lift, Syntax5.{ ctag; rhs = cmds1 @ cmds2 @ [ Break ] }))
      lift cases
  in
  (cases, lift)

let trans_dcls dcls : Syntax5.prog =
  let rec aux ctx lift = function 
    | [] -> (lift, [], Syntax5.NULL)
    | Main { cmds; ret } :: _ ->
      let lhs = Name.mk "x" in
      let cmds, lift = trans_cmds ctx lift cmds in
      let ret = trans_expr ret in
      Syntax5.(lift, cmds @ [ Force (lhs, ret) ], Var lhs)
    | DefFun { fn; args; cmds; ret } :: rest ->
      let xs = List.map snd args in
      let fname0 = Name.(mk ("fn0_" ^ name_of fn)) in
      let fname1 = Name.(mk ("fn1_" ^ name_of fn)) in
      let argc = List.length args in
      let ctx = Ctx.add fn fname0 argc ctx in
      let ret0 = trans_expr ret in
      let cmds0, lift = trans_cmds ctx lift cmds in
      let args1 = List.map (fun x -> Syntax5.Var x) xs in
      let ret1 = Name.mk "x" in
      let cmds1 = List.mapi (fun i (_, x) -> Syntax5.(Env (x, i + 1))) args in
      let cmds1 = cmds1 @ [ AppF { lhs = ret1; fn = fname0; args = args1 } ] in
      let lift, rest, r = aux ctx lift rest in
      Syntax5.
        ( DefFun0
            { fn = fname0
            ; args = xs
            ; cmds = cmds0
            ; ret = ret0
            } ::
          DefFun1
            { fn = fname1
            ; cmds = cmds1
            ; ret = Var ret1
            }
          :: lift
        , MkClo0
            { lhs = fn
            ; fn = fname1
            ; fvc = 0
            ; argc
            } :: rest, r )
    | DefVal { lhs; cmds; ret = rhs } :: rest ->
      let cmds, lift = trans_cmds ctx lift cmds in
      let rhs = trans_expr rhs in
      let lift, rest, r = aux ctx lift rest in
      Syntax5.(lift, cmds @ [ Move0 (lhs, rhs) ] @ rest, r)
  in
  let lift, cmds, ret = aux Ctx.empty [] dcls in
  Syntax5.{ dcls = lift; cmds; ret }
