open Fmt
open Bindlib
open Syntax1
open Context1e
open Equality1e
open Pprint1

module IPrbm = struct
  type eqn =
    | EqualSort of sort * sort
    | EqualTerm of Env.t * tm * tm

  type eqns = eqn list

  let pp_eqn fmt = function
    | EqualSort (s1, s2) ->
      pf fmt "@[equal_sort?@;<1 2>(%a,@;<1 2>%a)@]" pp_sort s1 pp_sort s2
    | EqualTerm (_, m1, m2) ->
      pf fmt "@[equal_tm?@;<1 2>(%a,@;<1 2>%a)@]" pp_tm m1 pp_tm m2

  let pp_eqns fmt eqns =
    let rec aux fmt = function
      | [] -> ()
      | [ eqn ] -> pp_eqn fmt eqn
      | eqn :: eqns -> pf fmt "%a;@;<1 0>%a" pp_eqn eqn aux eqns
    in
    pf fmt "@[<v 0>eqns {|@;<1 2>@[<v 0>%a@]@;<1 0>|}@]" aux eqns
end

module PPrbm = struct
  type eqn =
    | EqualPat of Env.t * tm * p * tm
    (* left: pattern type, right: checked type *)
    | EqualTerm of Env.t * tm * tm

  and eqns = eqn list

  type t =
    { global : eqns
    ; clause : (eqns * ps * tm option * ps) list
    }

  let rec of_cls (cls : cls) : t =
    match cls with
    | [] -> { global = []; clause = [] }
    | (p0s, bnd) :: cls ->
      let xs, rhs = unmbind_pmeta bnd in
      let _, ps = ps_of_mvar (Array.to_list xs) p0s in
      let prbm = of_cls cls in
      { prbm with clause = ([], ps, rhs, []) :: prbm.clause }

  let pp_eqn fmt = function
    | EqualPat (_, m, p, a) ->
      pf fmt "@[eq_pat?(@;<1 2>%a,@;<1 2>%a :@;<1 2>%a)@]" pp_tm m pp_p p pp_tm
        a
    | EqualTerm (_, a, b) ->
      pf fmt "@[eq_term?(@;<1 2>%a,@;<1 2>%a)@]" pp_tm a pp_tm b

  let pp_eqns fmt eqns =
    let rec aux fmt = function
      | [] -> ()
      | [ prbm ] -> pp_eqn fmt prbm
      | prbm :: prbms -> pf fmt "@[%a@]@;<1 0>%a" pp_eqn prbm aux prbms
    in
    pf fmt "@[<v 0>%a@]" aux eqns

  let pp_clause fmt (prbms, ps, opt, _) =
    match opt with
    | Some rhs ->
      pf fmt "@[{| @[%a ::: [%a] =>?@;<1 2>%a@]@;<1 0>|}@]" pp_eqns prbms
        (pp_ps ", ") ps pp_tm rhs
    | None -> pf fmt "(%a) ::: [%a] =>? !!" pp_eqns prbms (pp_ps ", ") ps

  let rec pp_clauses fmt = function
    | [] -> ()
    | [ clause ] -> pp_clause fmt clause
    | clause :: clauses ->
      pf fmt "%a@;<1 0>%a" pp_clause clause pp_clauses clauses

  let pp fmt = function
    | { global; clause } ->
      pf fmt "@[prblm {|@;<1 2>@[%a@];@;<1 2>@[%a@]@;<1 0>|}@]" pp_eqns global
        pp_clauses clause
end
