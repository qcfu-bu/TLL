open Bindlib
open Names
open Syntax2

let rec eq_tm m1 m2 =
  match (m1, m2) with
  (* core *)
  | Var x1, Var x2 -> eq_vars x1 x2
  | Const x1, Const x2 -> Const.equal x1 x2
  | Fun (relvs1, bnd1), Fun (relvs2, bnd2) ->
    relvs1 = relvs2 && eq_binder (eq_mbinder eq_tm) bnd1 bnd2
  | App (s1, m1, n1), App (s2, m2, n2) -> s1 = s2 && eq_tm m1 m2 && eq_tm n1 n2
  | Let (m1, bnd1), Let (m2, bnd2) -> eq_tm m1 m2 && eq_binder eq_tm bnd1 bnd2
  (* inductive *)
  | Constr (c1, ms1), Constr (c2, ms2) ->
    Constr.equal c1 c2 && List.equal eq_tm ms1 ms2
  | Match (relv1, s1, m1, cls1), Match (relv2, s2, m2, cls2) ->
    relv1 = relv2 && s1 = s2 && eq_tm m1 m2
    && List.equal
         (fun (c1, bnd1) (c2, bnd2) ->
           Constr.equal c1 c2 && eq_mbinder eq_tm bnd1 bnd2)
         cls1 cls2
  | Absurd, Absurd -> true
  (* monad *)
  | Return m1, Return m2 -> eq_tm m1 m2
  | MLet (m1, bnd1), MLet (m2, bnd2) -> eq_tm m1 m2 && eq_binder eq_tm bnd1 bnd2
  (* erasure *)
  | NULL, NULL -> true
  (* magic *)
  | Magic, Magic -> true
  | _ -> false
