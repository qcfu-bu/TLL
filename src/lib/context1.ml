open Bindlib
open Names
open Syntax1

module Ctx = struct
  type t =
    { var : tm Var.Map.t
    ; svar : SVar.Set.t
    ; const : (tm * tm) scheme Const.Map.t
    ; ind : (tele * dconstrs) param scheme Ind.Map.t
    ; constr : tele param scheme Constr.Map.t
    }

  let empty =
    { var = Var.Map.empty
    ; svar = SVar.Set.empty
    ; const = Const.Map.empty
    ; ind = Ind.Map.empty
    ; constr = Constr.Map.empty
    }

  let add_var x a (ctx : t) = { ctx with var = Var.Map.add x a ctx.var }
  let add_svar x (ctx : t) = { ctx with svar = SVar.Set.add x ctx.svar }

  let add_const x sch (ctx : t) =
    { ctx with const = Const.Map.add x sch ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch (ctx : t) =
    { ctx with constr = Constr.Map.add x sch ctx.constr }

  let find_var x (ctx : t) = Var.Map.find x ctx.var
  let find_const x (ctx : t) = Const.Map.find x ctx.const
  let find_ind x (ctx : t) = Ind.Map.find x ctx.ind
  let find_constr x (ctx : t) = Constr.Map.find x ctx.constr
end

module MCtx = struct
  type t = tm IMeta.Map.t

  let empty = IMeta.Map.empty
  let add_imeta x a (mctx : t) = IMeta.Map.add x a mctx
  let find_imeta x (mctx : t) = IMeta.Map.find_opt x mctx
end
