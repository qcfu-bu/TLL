open Fmt
open Syntax1
open Context1
open Equality1
open Pprint1

module IPrbm = struct
  type prbm =
    | EqualSort of sort * sort
    | EqualTerm of Ctx.t * tm * tm
    | CheckType of Ctx.t * tm * tm
    | AssertType of Ctx.t * tm

  type t = prbm list

  let pp_prbm fmt = function
    | EqualSort (s1, s2) ->
      pf fmt "@[equal_sort?@;<1 2>(%a,@;<1 2>%a)@]" pp_sort s1 pp_sort s2
    | EqualTerm (_, m1, m2) ->
      pf fmt "@[equal_tm?@;<1 2>(%a,@;<1 2>%a)@]" pp_tm m1 pp_tm m2
    | CheckType (_, m, a) ->
      pf fmt "@[check?@;<1 2>(%a,@;<1 2>%a)@]" pp_tm m pp_tm a
    | AssertType (_, a) -> pf fmt "@[assert_type?@;<1 2>(%a)@]" pp_tm a

  let rec pp fmt = function
    | [] -> ()
    | [ prbm ] -> pp_prbm fmt prbm
    | prbm :: prbms -> pf fmt "%a;@;<1 0>%a" pp_prbm prbm pp prbms
end

module PPrbm = struct
  type prbm = EqTm of Ctx.t * tm * tm * tm
  and prbms = prbm list

  type t =
    { global : prbms
    ; clause : (prbms * ps * tm option) list
    }

  let pp_prbm fmt = function
    | EqTm (_, m, n, a) ->
      pf fmt "@[eq_tm?@;<1 2>(%a,@;<1 2>%a :@;<1 2>%a)@]" pp_tm m pp_tm n pp_tm
        a

  let rec pp_prbms fmt = function
    | [] -> ()
    | [ prbm ] -> pp_prbm fmt prbm
    | prbm :: prbms -> pf fmt "%a@;<1 0>%a" pp_prbm prbm pp_prbms prbms

  let pp_clause fmt (prbms, ps, opt) =
    match opt with
    | Some rhs ->
      pf fmt "(%a) ::: (%a) =>? %a" pp_prbms prbms (pp_ps ", ") ps pp_tm rhs
    | None -> pf fmt "(%a) ::: (%a) =>? !!" pp_prbms prbms (pp_ps ", ") ps

  let rec pp_clauses fmt = function
    | [] -> ()
    | [ clause ] -> pp_clause fmt clause
    | clause :: clauses ->
      pf fmt "%a@;<1 0>%a" pp_clause clause pp_clauses clauses

  let pp fmt = function
    | { global; clause } ->
      pf fmt "prblm {| %a; %a |}" pp_prbms global pp_clauses clause
end
