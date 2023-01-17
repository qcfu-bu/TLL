From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_val : term -> Prop :=
| dyn_val_var x : dyn_val (Var x)
| dyn_val_lam0 A B s : dyn_val (Lam0 A B s)
| dyn_val_lam1 A B s : dyn_val (Lam1 A B s)
| dyn_val_it : dyn_val It
| dyn_val_num n : dyn_val (Num n)
| dyn_val_rand : dyn_val Rand
| dyn_val_randit : dyn_val (App Rand It)
| dyn_val_return v : dyn_val v -> dyn_val (Return v)
| dyn_val_letin v n : dyn_val v -> dyn_val (LetIn v n).

Reserved Notation "m ~>> n" (at level 50).
Inductive dyn_step : term -> term -> Prop :=
| dyn_appL m m' n :
  m ~>> m' ->
  App m n ~>> App m' n
| dyn_appR m n n' :
  n ~>> n' ->
  App m n ~>> App m n'
| dyn_beta0 A m n s :
  App (Lam0 A m s) n ~>> m.[n/]
| dyn_beta1 A m v s :
  dyn_val v ->
  App (Lam1 A m s) v ~>> m.[v/]
| dyn_return m m' :
  m ~>> m' ->
  Return m ~>> Return m'
| dyn_letinL m m' n :
  m ~>> m' ->
  LetIn m n ~>> LetIn m' n
where "m ~>> n" := (dyn_step m n).

Notation dyn_red := (star dyn_step).
Notation "m ~>>* n" := (dyn_red m n) (at level 50).

Inductive dyn_mval : term -> Prop :=
| dyn_mval_var x : dyn_mval (Var x)
| dyn_mval_lam0 A B s : dyn_mval (Lam0 A B s)
| dyn_mval_lam1 A B s : dyn_mval (Lam1 A B s)
| dyn_mval_it : dyn_mval It
| dyn_mval_num n : dyn_mval (Num n)
| dyn_mval_rand : dyn_mval Rand
| dyn_mval_return v : dyn_val v -> dyn_mval (Return v).

Reserved Notation "R ; m ~>> T ; n" (at level 50, m, T, n at next level).
Inductive dyn_mstep : (nat * term) -> (nat * term) -> Prop :=
| dyn_mstep_step R m m' :
  m ~>> m' ->
  R ; m ~>> R ; m'
| dyn_mstep_rand R :
  R ; App Rand It ~>> R.+1 ; Return (Num R)
| dyn_mstep_letin R T m m' n :
  R ; m ~>> T ; m' ->
  R ; LetIn m n ~>> T ; LetIn m' n
| dyn_mstep_letret R v n :
  dyn_val v ->
  R ; LetIn (Return v) n ~>> R ; n.[v/]
where "R ; m ~>> T ; n" := (dyn_mstep (R, m) (T, n)).

Lemma dyn_mval_val m : dyn_mval m -> dyn_val m.
Proof with eauto using dyn_val. elim=>{m}... Qed.

Lemma dyn_val_terminal m : dyn_val m -> ~exists n, m ~>> n.
Proof.
  elim=>{m}.
  { move=>x[n st]. inv st. }
  { move=>A B s[n st]. inv st. }
  { move=>A B s[n st]. inv st. }
  { move=>[n st]. inv st. }
  { move=>n[x st]. inv st. }
  { move=>[n st]. inv st. }
  { move=>[n st]. inv st. inv H2. inv H2. }
  { move=>v vl ih[n st]. inv st.
    apply: ih. by exists m'. }
  { move=>v n vl ih[n0 st]. inv st.
    apply: ih. by exists m'. }
Qed.

Lemma dyn_mval_terminal R m : dyn_mval m -> ~exists T n, R ; m ~>> T ; n.
Proof.
  move=>vl. elim: vl R=>{m}.
  { move=>x R[T[n st]]. inv st. inv H0. }
  { move=>A B s R[T[n st]]. inv st. inv H0. }
  { move=>A B s R[T[n st]]. inv st. inv H0. }
  { move=>R[T[n st]]. inv st. inv H0. }
  { move=>n R[T[n0 st]]. inv st. inv H0. }
  { move=>R[T[n st]]. inv st. inv H0. }
  { move=>v vl ih[T[n st]]. inv st. inv H0.
    apply: dyn_val_terminal.
    apply: vl. by exists m'. }
Qed.
