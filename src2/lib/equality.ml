open Bindlib
open Names
open Syntax1

type rd = Beta | Delta | Zeta | Iota

let enabled mode rd = Array.exists (( = ) rd) mode

let rec whnf mode env = function
  (* inference *)
  | Ann (m, a) -> whnf mode env m
  (* core *)
  | Var x ->
      if enabled mode Delta then
        match VMap.find_opt x env with
        | Some m -> whnf mode env m
        | None -> Var x
      else Var x
  | App (m, n) ->
      let m = whnf mode env m in
      let n = whnf mode env n in
      if enabled mode Beta then
        match m with
        | Lam (_, _, bnd) -> whnf mode env (subst bnd n)
        | Fix (r, bnd) -> whnf mode env (App (subst bnd (Var r), n))
        | _ -> App (m, n)
      else App (m, n)
  | Let (r, m, bnd) ->
      if enabled mode Zeta then
        let m = whnf mode env m in
        let x, n = unbind bnd in
        whnf mode (VMap.add x m env) n
      else Let (r, m, bnd)
  | _ -> failwith "other"
