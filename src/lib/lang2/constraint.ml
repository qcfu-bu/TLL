open Syntax
open Context
open Environment

(* constraints for implicit inference *)
module IConstraint = struct
  type eqn =
    | EqSort of sort * sort
    | EqTm of Env.t * tm * tm
    | Check of Ctx.t * Env.t * tm * tm
    | Search of Ctx.t * Env.t * tm * tm

  type t = eqn list
end

(* constraints for dependent pattern matching *)
module PConstraint = struct
  type eqn = Eq of Ctx.t * Env.t * tm * tm * tm
  and eqns = eqn list

  type t =
    { global : eqns
    ; clause : (eqns * ps * tm) list
    }
end
