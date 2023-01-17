From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ; Δ ⊢ m ~ n : A" (at level 50, Δ, m, n, A at next level).
Inductive era_type : sta_ctx -> dyn_ctx -> term -> term -> term -> Prop :=
| era_var Γ Δ x s A :
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x s A ->
  Γ ; Δ ⊢ Var x ~ Var x : A
| era_lam0 Γ Δ A B m m' s :
  Δ ▷ s ->
  (A :: Γ) ; _: Δ ⊢ m ~ m' : B ->
  Γ ; Δ ⊢ Lam0 A m s ~ Lam0 Box m' s : Pi0 A B s
| era_lam1 Γ Δ A B m m' s t :
  Δ ▷ s ->
  (A :: Γ) ; A :{t} Δ ⊢ m ~ m' : B ->
  Γ ; Δ ⊢ Lam1 A m s ~ Lam1 Box m' s : Pi1 A B s
| era_app0 Γ Δ A B m m' n s :
  Γ ; Δ ⊢ m ~ m' : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ; Δ ⊢ App m n ~ App m' Box : B.[n/]
| era_app1 Γ Δ1 Δ2 Δ A B m m' n n' s :
  Δ1 ∘ Δ2 => Δ ->
  Γ ; Δ1 ⊢ m ~ m' : Pi1 A B s ->
  Γ ; Δ2 ⊢ n ~ n' : A ->
  Γ ; Δ ⊢ App m n ~ App m' n' : B.[n/]
| era_it Γ Δ :
  Δ ▷ U ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ It ~ It : Unit
| era_num Γ Δ n :
  Δ ▷ U ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ Num n ~ Num n : Nat
| era_rand Γ Δ :
  Δ ▷ U ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ Rand ~ Rand : Pi1 Unit (IO Nat) U
| era_return Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A ->
  Γ ; Δ ⊢ Return m ~ Return m' : IO A
| era_letin Γ Δ1 Δ2 Δ m m' n n' A B s t :
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ B : Sort t ->
  Γ ; Δ1 ⊢ m ~ m' : IO A ->
  (A :: Γ) ; (A :{s} Δ2) ⊢ n ~ n' : IO B.[ren (+1)] ->
  Γ ; Δ ⊢ LetIn m n ~ LetIn m' n' : IO B
| era_conv Γ Δ A B m m' s :
  A === B ->
  Γ ; Δ ⊢ m ~ m' : A ->
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m ~ m' : B
where "Γ ; Δ ⊢ m ~ n : A" := (era_type Γ Δ m n A).

Lemma era_dyn_type Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_type. elim... Qed.

Lemma dyn_era_type Γ Δ m A :
  Γ ; Δ ⊢ m : A -> exists m', Γ ; Δ ⊢ m ~ m' : A.
Proof with eauto using era_type.
  elim=>{Γ Δ m A}.
  { move=>Γ Δ x A wf shs dhs. exists (Var x)... }
  { move=>Γ Δ A B m s k tym[m' er].
    exists (Lam0 Box m' s)... }
  { move=>Γ Δ A B m s t k tym[m' er].
    exists (Lam1 Box m' s)... }
  { move=>Γ Δ A B m n s tym[m' er]tyn.
    exists (App m' Box).
    apply: era_app0... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym[m' erm]tyn[n' ern].
    exists (App m' n').
    apply: era_app1... }
  { move=>Γ Δ k wf. exists It... }
  { move=>Γ Δ n k wf. exists (Num n)... }
  { move=>Γ Δ k wf. exists Rand... }
  { move=>Γ Δ m A tym[m' erm]. exists (Return m')... }
  { move=>Γ Δ1 Δ2 Δ m n A B s t mrg tyB tym[m' erm]tyn[n' ern].
    exists (LetIn m' n')... }
  { move=>Γ Δ A B m s eq tym[m' er]tyB.
    exists m'. apply: era_conv... }
Qed.
