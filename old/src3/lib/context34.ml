open Fmt
open Bindlib
open Names
open Syntax3

module Ctx = struct
  type t =
    { var : Syntax4.expr Var.Map.t
    ; const : Syntax4.expr Const.Map.t
    }

  let empty = { var = Var.Map.empty; const = Const.Map.empty }

  let find_var x (ctx : t) = 
    try Var.Map.find x ctx.var
    with _ -> failwith "trans34.find_var(%a)" Var.pp x

  let find_const x (ctx : t) =
    try Const.Map.find x ctx.const
    with _ -> failwith "trans34.find_const(%a)" Const.pp x

  let add_var x n (ctx : t) = 
    Debug.exec (fun () -> pr "add_var(%a)@." Var.pp x);
    { ctx with var = Var.Map.add x n ctx.var }

  let add_const x n (ctx : t) = 
    Debug.exec (fun () -> pr "add_const(%a)@." Const.pp x);
    { ctx with const = Const.Map.add x n ctx.const }
end


