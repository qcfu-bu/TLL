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
    relv1 = relv2 && s1 = s2 && eq_tm m1 m2 &&
    List.equal (fun (c1, bnd1) (c2, bnd2) ->
        Constr.equal c1 c2 && eq_mbinder eq_tm bnd1 bnd2)
      cls1 cls2
  | Absurd, Absurd -> true
  (* monad *)
  | Return m1, Return m2 -> eq_tm m1 m2
  | MLet (m1, bnd1), MLet (m2, bnd2) -> eq_tm m1 m2 && eq_binder eq_tm bnd1 bnd2
  (* primitive terms *)
  | Int i1, Int i2 -> i1 = i2
  | Char c1, Char c2 -> c1 = c2
  | String s1, String s2 -> s1 = s2
  (* primitive operators *)
  | Neg m1, Neg m2 -> eq_tm m1 m2
  | Add (m1, n1), Add (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Sub (m1, n1), Sub (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Mul (m1, n1), Mul (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Div (m1, n1), Div (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Mod (m1, n1), Mod (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Lte (m1, n1), Lte (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Gte (m1, n1), Gte (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Lt (m1, n1), Lt (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Gt (m1, n1), Gt (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Eq (m1, n1), Eq (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Chr m1, Chr m2 -> eq_tm m1 m2
  | Ord m1, Ord m2 -> eq_tm m1 m2
  | Push (m1, n1), Push (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Cat (m1, n1), Cat (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  | Size m1, Size m2 -> eq_tm m1 m2
  | Indx (m1, n1), Indx (m2, n2) -> eq_tm m1 m2 && eq_tm n1 n2
  (* primitive effects *)
  | Print m1, Print m2 -> eq_tm m1 m2
  | Prerr m1, Prerr m2 -> eq_tm m1 m2
  | ReadLn m1, ReadLn m2 -> eq_tm m1 m2
  | Fork m1, Fork m2 -> eq_tm m1 m2
  | Send (relv1, s1, m1), Send (relv2, s2, m2)
    when relv1 = relv2 && s1 = s2 -> eq_tm m1 m2
  | Recv (relv1, s1, m1), Recv (relv2, s2, m2)
    when relv1 = relv2 && s1 = s2 -> eq_tm m1 m2
  | Close (role1, m1), Close (role2, m2) when role1 = role2 -> eq_tm m1 m2
  (* erasure *)
  | NULL, NULL -> true
  (* magic *)
  | Magic, Magic -> true
  | _ -> false
