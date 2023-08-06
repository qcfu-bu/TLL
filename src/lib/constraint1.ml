open Fmt
open Syntax1
open Context1
open Equality1
open Pprint1

module IPrbm = struct
  type prbm =
    | EqSort of sort * sort
    | EqTm of Env.t * tm * tm
    | Check of Ctx.t * Env.t * tm * tm

  type t = prbm list

  let pp_prbm fmt = function
    | EqSort (s1, s2) ->
      pf fmt "@[eq_sort?@;<1 2>(%a,@;<1 2>%a)@]" pp_sort s1 pp_sort s2
    | EqTm (_, m1, m2) ->
      pf fmt "@[eq_tm?@;<1 2>(%a,@;<1 2>%a)@]" pp_tm m1 pp_tm m2
    | Check (_, _, m, a) ->
      pf fmt "@[check?@;<1 2>(%a,@;<1 2>%a)@]" pp_tm m pp_tm a

  let rec pp fmt = function
    | [] -> ()
    | [ prbm ] -> pp_prbm fmt prbm
    | prbm :: prbms -> pf fmt "%a@.@.%a" pp_prbm prbm pp prbms
end

module PPrbm = struct
  type prbm = EqTm of Env.t * tm * tm * tm
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
