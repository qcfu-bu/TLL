open Names
open Syntax
open Util

module Env = struct
  type t =
    { var : tm Var.Map.t
    ; const : (sorts -> tm) Const.Map.t
    }

  let empty = { var = Var.Map.empty; const = Const.Map.empty }
  let find_var x env = Var.Map.find_opt x env.var
  let find_const x env = Const.Map.find_opt x env.const
  let add_var x m env = { env with var = Var.Map.add x m env.var }
  let add_const x m env = { env with const = Const.Map.add x m env.const }
end
