open Names
open Syntax
open Util

module Ctx = struct
  type t =
    { var : tm Var.Map.t
    ; svar : SVar.Set.t
    ; const : tm scheme Const.Map.t
    ; ind : (tm scheme * Constr.Set.t) Ind.Map.t
    ; constr : tm scheme Constr.Map.t
    }
end
