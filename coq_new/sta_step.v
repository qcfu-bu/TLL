From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast sta_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~> n" (at level 30).
Inductive sta_step : term -> term -> Prop :=
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
| sta_step_letin0A A A' m n :
  A ~> A' ->
  LetIn0 A m n ~> LetIn0 A' m n
| sta_step_letin0L A m m' n :
  m ~> m' ->
  LetIn0 A m n ~> LetIn0 A m' n
| sta_step_letin0R A m n n' :
  n ~> n' ->
  LetIn0 A m n ~> LetIn0 A m n'
| sta_step_letin1A A A' m n :
  A ~> A' ->
  LetIn1 A m n ~> LetIn1 A' m n
| sta_step_letin1L A m m' n :
  m ~> m' ->
  LetIn1 A m n ~> LetIn1 A m' n
| sta_step_letin1R A m n n' :
  n ~> n' ->
  LetIn1 A m n ~> LetIn1 A m n'
| sta_step_iota0 A m1 m2 n s :
  LetIn0 A (Pair0 m1 m2 s) n ~> n.[m2,m1/]
| sta_step_iota1 A m1 m2 n s :
  LetIn1 A (Pair1 m1 m2 s) n ~> n.[m2,m1/]
| sta_step_withL A A' B s :
  A ~> A' ->
  With A B s ~> With A' B s
| sta_step_withR A B B' s :
  B ~> B' ->
  With A B s ~> With A B' s
| sta_step_apairL m m' n s :
  m ~> m' ->
  APair m n s ~> APair m' n s
| sta_step_apairR m n n' s :
  n ~> n' ->
  APair m n s ~> APair m n' s
| sta_step_fst m m' :
  m ~> m' ->
  Fst m ~> Fst m'
| sta_step_snd m m' :
  m ~> m' ->
  Snd m ~> Snd m'
| sta_step_proj1 m n s :
  Fst (APair m n s) ~> m
| sta_step_proj2 m n s :
  Snd (APair m n s) ~> n
| sta_step_idA A A' m n :
  A ~> A' ->
  Id A m n ~> Id A' m n
| sta_step_idL A m m' n :
  m ~> m' ->
  Id A m n ~> Id A m' n
| sta_step_idR A m n n' :
  n ~> n' ->
  Id A m n ~> Id A m n'
| sta_step_refl m m' :
  m ~> m' ->
  Refl m ~> Refl m'
| sta_step_rewA A A' H P :
  A ~> A' ->
  Rew A H P ~> Rew A' H P
| sta_step_rewH A H H' P :
  H ~> H' ->
  Rew A H P ~> Rew A H' P
| sta_step_rewP A H P P' :
  P ~> P' ->
  Rew A H P ~> Rew A H P'
| sta_step_rewR A H m :
  Rew A H (Refl m) ~> H.[m/]
where "m ~> n" := (sta_step m n).

Notation sta_red := (star sta_step).
Notation "m ~>* n" := (sta_red m n) (at level 30).
Notation "m === n" := (conv sta_step m n) (at level 50).
