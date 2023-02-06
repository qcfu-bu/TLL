From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast sta_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~> n" (at level 50).
Inductive sta_step : term -> term -> Prop :=
(* core *)
| sta_step_pi0L A A' B s :
  A ~> A' ->
  Pi0 A B s ~> Pi0 A' B s
| sta_step_pi1L A A' B s :
  A ~> A' ->
  Pi1 A B s ~> Pi1 A' B s
| sta_step_pi0R A B B' s :
  B ~> B' ->
  Pi0 A B s ~> Pi0 A B' s
| sta_step_pi1R A B B' s :
  B ~> B' ->
  Pi1 A B s ~> Pi1 A B' s
| sta_step_lam0L A A' m s :
  A ~> A' ->
  Lam0 A m s ~> Lam0 A' m s
| sta_step_lam1L A A' m s :
  A ~> A' ->
  Lam1 A m s ~> Lam1 A' m s
| sta_step_lam0R A m m' s :
  m ~> m' ->
  Lam0 A m s ~> Lam0 A m' s
| sta_step_lam1R A m m' s :
  m ~> m' ->
  Lam1 A m s ~> Lam1 A m' s
| sta_step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| sta_step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| sta_step_beta0 A m n s :
  App (Lam0 A m s) n ~> m.[n/]
| sta_step_beta1 A m n s :
  App (Lam1 A m s) n ~> m.[n/]
| sta_step_sig0L A A' B s :
  A ~> A' ->
  Sig0 A B s ~> Sig0 A' B s
| sta_step_sig0R A B B' s :
  B ~> B' ->
  Sig0 A B s ~> Sig0 A B' s
| sta_step_sig1L A A' B s :
  A ~> A' ->
  Sig1 A B s ~> Sig1 A' B s
| sta_step_sig1R A B B' s :
  B ~> B' ->
  Sig1 A B s ~> Sig1 A B' s
| sta_step_pair0L m m' n s :
  m ~> m' ->
  Pair0 m n s ~> Pair0 m' n s
| sta_step_pair0R m n n' s :
  n ~> n' ->
  Pair0 m n s ~> Pair0 m n' s
| sta_step_pair1L m m' n s :
  m ~> m' ->
  Pair1 m n s ~> Pair1 m' n s
| sta_step_pair1R m n n' s :
  n ~> n' ->
  Pair1 m n s ~> Pair1 m n' s
| sta_step_letinA A A' m n :
  A ~> A' ->
  LetIn A m n ~> LetIn A' m n
| sta_step_letinL A m m' n :
  m ~> m' ->
  LetIn A m n ~> LetIn A m' n
| sta_step_letinR A m n n' :
  n ~> n' ->
  LetIn A m n ~> LetIn A m n'
| sta_step_letinE0 A m1 m2 n s :
  LetIn A (Pair0 m1 m2 s) n ~> n.[m2,m1/]
| sta_step_letinE1 A m1 m2 n s :
  LetIn A (Pair1 m1 m2 s) n ~> n.[m2,m1/]
| sta_step_fixL A A' m :
  A ~> A' ->
  Fix A m ~> Fix A' m
| sta_step_fixR A m m' :
  m ~> m' ->
  Fix A m ~> Fix A m'
| sta_step_fixE A m :
  Fix A m ~> m.[Fix A m/]
(* data *)
| sta_step_ifteA A A' m n1 n2 :
  A ~> A' ->
  Ifte A m n1 n2 ~> Ifte A' m n1 n2
| sta_step_ifteM A m m' n1 n2 :
  m ~> m' ->
  Ifte A m n1 n2 ~> Ifte A m' n1 n2
| sta_step_ifteN1 A m n1 n1' n2 :
  n1 ~> n1' ->
  Ifte A m n1 n2 ~> Ifte A m n1' n2
| sta_step_ifteN2 A m n1 n2 n2' :
  n2 ~> n2' ->
  Ifte A m n1 n2 ~> Ifte A m n1 n2'
| sta_step_ifteT A n1 n2 :
  Ifte A TT n1 n2 ~> n1
| sta_step_ifteF A n1 n2 :
  Ifte A FF n1 n2 ~> n2
(* monadic *)
| sta_step_io A A' :
  A ~> A' ->
  IO A ~> IO A'
| sta_step_return m m' :
  m ~> m' ->
  Return m ~> Return m'
| sta_step_bindL m m' n :
  m ~> m' ->
  Bind m n ~> Bind m' n
| sta_step_bindR m n n' :
  n ~> n' ->
  Bind m n ~> Bind m n'
| sta_step_bindE m n :
  Bind (Return m) n ~> n.[m/]
(* session *)
| sta_step_act0L r A A' B :
  A ~> A' ->
  Act0 r A B ~> Act0 r A' B
| sta_step_act0R r A B B' :
  B ~> B' ->
  Act0 r A B ~> Act0 r A B'
| sta_step_act1L r A A' B :
  A ~> A' ->
  Act1 r A B ~> Act1 r A' B
| sta_step_act1R r A B B' :
  B ~> B' ->
  Act1 r A B ~> Act1 r A B'
| sta_step_ch r A A' :
  A ~> A' ->
  Ch r A ~> Ch r A'
| sta_step_forkL A A' m :
  A ~> A' ->
  Fork A m ~> Fork A' m
| sta_step_forkR A m m' :
  m ~> m' ->
  Fork A m ~> Fork A m'
| sta_step_recv m m' :
  m ~> m' ->
  Recv m ~> Recv m'
| sta_step_send m m' :
  m ~> m' ->
  Send m ~> Send m'
| sta_step_close m m' :
  m ~> m' ->
  Close m ~> Close m'
| sta_step_wait m m' :
  m ~> m' ->
  Wait m ~> Wait m'
where "m ~> n" := (sta_step m n).

Notation sta_red := (star sta_step).
Notation "m ~>* n" := (sta_red m n) (at level 50).
Notation "m === n" := (conv sta_step m n) (at level 50).
