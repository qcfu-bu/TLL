open Fmt
open Syntax1
open Context1
open Equality1
open Pprint1

module IPrbm = struct
  type eqn =
    | EqualSort of sort * sort
    | EqualTerm of Ctx.t * tm * tm

  type eqns = eqn list

  let pp_eqn fmt = function
    | EqualSort (s1, s2) ->
      pf fmt "@[equal_sort?@;<1 2>(%a,@;<1 2>%a)@]" pp_sort s1 pp_sort s2
    | EqualTerm (_, m1, m2) ->
      pf fmt "@[equal_tm?@;<1 2>(%a,@;<1 2>%a)@]" pp_tm m1 pp_tm m2

  let rec pp_eqns fmt = function
    | [] -> ()
    | [ eqn ] -> pp_eqn fmt eqn
    | eqn :: eqns -> pf fmt "%a;@;<1 0>%a" pp_eqn eqn pp_eqns eqns
end

module PPrbm = struct
  type eqn = EqTm of Ctx.t * tm * tm * tm
  and eqns = eqn list

  type t =
    { global : eqns
    ; clause : (eqns * ps * tm option) list
    }

  let pp_eqn fmt = function
    | EqTm (_, m, n, a) ->
      pf fmt "@[eq_tm?@;<1 2>(%a,@;<1 2>%a :@;<1 2>%a)@]" pp_tm m pp_tm n pp_tm
        a

  let rec pp_eqns fmt = function
    | [] -> ()
    | [ prbm ] -> pp_eqn fmt prbm
    | prbm :: prbms -> pf fmt "%a@;<1 0>%a" pp_eqn prbm pp_eqns prbms

  let pp_clause fmt (prbms, ps, opt) =
    match opt with
    | Some rhs ->
      pf fmt "(%a) ::: (%a) =>? %a" pp_eqns prbms (pp_ps ", ") ps pp_tm rhs
    | None -> pf fmt "(%a) ::: (%a) =>? !!" pp_eqns prbms (pp_ps ", ") ps

  let rec pp_clauses fmt = function
    | [] -> ()
    | [ clause ] -> pp_clause fmt clause
    | clause :: clauses ->
      pf fmt "%a@;<1 0>%a" pp_clause clause pp_clauses clauses

  let pp fmt = function
    | { global; clause } ->
      pf fmt "prblm {| %a; %a |}" pp_eqns global pp_clauses clause
end
