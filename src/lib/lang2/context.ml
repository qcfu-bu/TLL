open Bindlib
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
    ; record : (tm * (tm, fields) mbinder) scheme Record.Map.t
    }

  let add_var x a (ctx : t) = { ctx with var = Var.Map.add x a ctx.var }
  let add_svar x (ctx : t) = { ctx with svar = SVar.Set.add x ctx.svar }

  let add_const x sch (ctx : t) =
    { ctx with const = Const.Map.add x sch ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch (ctx : t) =
    { ctx with constr = Constr.Map.add x sch ctx.constr }

  let add_record x sch (ctx : t) =
    { ctx with record = Record.Map.add x sch ctx.record }

  let find_var x (ctx : t) = Var.Map.find x ctx.var
  let find_const x (ctx : t) = Const.Map.find x ctx.const
  let find_ind x (ctx : t) = Ind.Map.find x ctx.ind
  let find_constr x (ctx : t) = Constr.Map.find x ctx.constr
  let find_record x (ctx : t) = Record.Map.find x ctx.record
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

  let find_imeta x (mctx : t) = IMeta.Map.find_opt x mctx.imeta
  let find_tmeta x (mctx : t) = TMeta.Map.find_opt x mctx.tmeta
end
