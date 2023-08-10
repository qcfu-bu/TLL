open Fmt
open Bindlib
open Names
open Syntax1

module Ctx : sig
  type t

  val empty : t
  val add_var0 : Var.t -> tm -> t -> t
  val add_var1 : Var.t -> tm -> tm -> t -> t
  val add_svar : SVar.t -> t -> t
  val add_const : Const.t -> (tm * tm) scheme -> t -> t
  val add_ind : Ind.t -> tele param scheme * Constr.t list -> t -> t
  val add_constr : Constr.t -> tele param scheme * mode -> t -> t
  val find_var0 : Var.t -> t -> tm
  val find_var1 : Var.t -> t -> tm option
  val find_svar : SVar.t -> t -> SVar.t
  val find_const : Const.t -> t -> (tm * tm) scheme
  val find_ind : Ind.t -> t -> tele param scheme * Constr.t list
  val find_constr : Constr.t -> t -> tele param scheme * mode
  val spine_var : t -> Var.t list
  val spine_svar : t -> SVar.t list
  val subst_fvar : tm Var.Map.t -> t -> t
end = struct
  type t =
    { var : (tm option * tm) Var.Map.t
    ; svar : SVar.Set.t
    ; const : (tm * tm) scheme Const.Map.t
    ; ind : (tele param scheme * Constr.t list) Ind.Map.t
    ; constr : (tele param scheme * mode) Constr.Map.t
    }

  let empty =
    { var = Var.Map.empty
    ; svar = SVar.Set.empty
    ; const = Const.Map.empty
    ; ind = Ind.Map.empty
    ; constr = Constr.Map.empty
    }

  let add_var0 x a (ctx : t) =
    { ctx with var = Var.Map.add x (None, a) ctx.var }

  let add_var1 x m a (ctx : t) =
    { ctx with var = Var.Map.add x (Some m, a) ctx.var }

  let add_svar x (ctx : t) = { ctx with svar = SVar.Set.add x ctx.svar }

  let add_const x sch (ctx : t) =
    { ctx with const = Const.Map.add x sch ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch ctx =
    { ctx with constr = Constr.Map.add x sch ctx.constr }

  let find_var0 x (ctx : t) = snd (Var.Map.find x ctx.var)
  let find_var1 x (ctx : t) : tm option = fst (Var.Map.find x ctx.var)
  let find_svar x (ctx : t) : SVar.t = SVar.Set.find x ctx.svar
  let find_const x (ctx : t) = Const.Map.find x ctx.const
  let find_ind x (ctx : t) = Ind.Map.find x ctx.ind
  let find_constr x (ctx : t) = Constr.Map.find x ctx.constr
  let spine_var (ctx : t) = ctx.var |> Var.Map.bindings |> List.map fst
  let spine_svar (ctx : t) = ctx.svar |> SVar.Set.elements

  let subst_fvar var_map (ctx : t) =
    let var =
      Var.Map.map
        (fun (m_opt, a) ->
          let m_opt = Option.map (subst_fvar var_map) m_opt in
          let a = subst_fvar var_map a in
          (m_opt, a))
        ctx.var
    in
    { ctx with var }
end

module MCtx : sig
  type t

  val empty : t
  val add_imeta : Ctx.t -> IMeta.t -> tm -> t -> t
  val find_imeta : IMeta.t -> t -> tm option
  val pp : t Fmt.t
end = struct
  type t = (Ctx.t * tm) IMeta.Map.t

  let empty = IMeta.Map.empty
  let add_imeta ctx x a (mctx : t) = IMeta.Map.add x (ctx, a) mctx

  let find_imeta x (mctx : t) =
    match IMeta.Map.find_opt x mctx with
    | Some (_, a) -> Some a
    | _ -> None

  let pp fmt mctx =
    let open Pprint1 in
    let rec aux fmt = function
      | [] -> ()
      | [ (x, (_, a)) ] -> pf fmt "?%a :? %a" IMeta.pp x pp_tm a
      | (x, (_, a)) :: ls ->
        pf fmt "?%a :? %a@;<1 0>%a" IMeta.pp x pp_tm a aux ls
    in
    aux fmt (IMeta.Map.bindings mctx)
end
