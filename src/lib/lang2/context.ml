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

  let add_var x a (ctx : t) = { ctx with var = Var.Map.add x a ctx.var }
  let add_svar x (ctx : t) = { ctx with svar = SVar.Set.add x ctx.svar }

  let add_const x sch (ctx : t) =
    { ctx with const = Const.Map.add x sch ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch (ctx : t) =
    { ctx with constr = Constr.Map.add x sch ctx.constr }
end

module MCtx = struct
  type t =
    { imeta : tm IMeta.Map.t
    ; tmeta : tm TMeta.Map.t
    }

  let add_imeta x a (mctx : t) =
    { mctx with imeta = IMeta.Map.add x a mctx.imeta }

  let add_tmeta x a (mctx : t) =
    { mctx with tmeta = TMeta.Map.add x a mctx.tmeta }
end
