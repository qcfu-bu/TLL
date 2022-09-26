From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta0_type : sta_ctx -> term -> term -> Prop :=
| sta0_axiom Γ s :
  sta0_wf Γ ->
  sta0_type Γ (Sort s) (Sort U)
| sta0_var Γ x A :
  sta0_wf Γ ->
  sta_has Γ x A ->
  sta0_type Γ (Var x) A
| sta0_pi0 Γ A B s r t :
  sta0_type Γ A (Sort r) ->
  sta0_type (A :: Γ) B (Sort t) ->
  sta0_type Γ (Pi0 A B s) (Sort s)
| sta0_pi1 Γ A B s r t :
  sta0_type Γ A (Sort r) ->
  sta0_type (A :: Γ) B (Sort t) ->
  sta0_type Γ (Pi1 A B s) (Sort s)
| sta0_lam0 Γ A B m s r :
  sta0_type Γ A (Sort r) ->
  sta0_type (A :: Γ) m B ->
  sta0_type Γ (Lam0 A m s) (Pi0 A B s)
| sta0_lam1 Γ A B m s r :
  sta0_type Γ A (Sort r) ->
  sta0_type (A :: Γ) m B ->
  sta0_type Γ (Lam1 A m s) (Pi1 A B s)
| sta0_app0 Γ A B m n s :
  sta0_type Γ m (Pi0 A B s) ->
  sta0_type Γ n A ->
  sta0_type Γ (App m n) B.[n/]
| sta0_app1 Γ A B m n s :
  sta0_type Γ m (Pi1 A B s) ->
  sta0_type Γ n A ->
  sta0_type Γ (App m n) B.[n/]
| sta0_conv Γ A B m s :
  A === B ->
  sta0_type Γ m A ->
  sta0_type Γ B (Sort s) ->
  sta0_type Γ m B

with sta0_wf : sta_ctx -> Prop :=
| sta0_wf_nil : sta0_wf nil
| sta0_wf_cons Γ A s :
  sta0_wf Γ ->
  sta0_type Γ A (Sort s) ->
  sta0_wf (A :: Γ).

Scheme sta0_type_mut := Induction for sta0_type Sort Prop
with sta0_wf_mut := Induction for sta0_wf Sort Prop.

Lemma sta0_type_wf Γ m A : sta0_type Γ m A -> sta0_wf Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
Hint Resolve sta0_type_wf.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive sta_type : sta_ctx -> term -> term -> Prop :=
| sta_axiom Γ s :
  sta_wf Γ ->
  Γ ⊢ Sort s : Sort U
| sta_var Γ x A :
  sta_wf Γ ->
  sta_has Γ x A ->
  Γ ⊢ Var x : A
| sta_pi0 Γ A B s t :
  (A :: Γ) ⊢ B : Sort t ->
  Γ ⊢ Pi0 A B s : Sort s
| sta_pi1 Γ A B s t :
  (A :: Γ) ⊢ B : Sort t ->
  Γ ⊢ Pi1 A B s : Sort s
| sta_lam0 Γ A B m s :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam0 A m s : Pi0 A B s
| sta_lam1 Γ A B m s :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam1 A m s : Pi1 A B s
| sta_app0 Γ A B m n s :
  Γ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| sta_app1 Γ A B m n s :
  Γ ⊢ m : Pi1 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| sta_conv Γ A B m s :
  A === B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (sta_type Γ m A)

with sta_wf : sta_ctx -> Prop :=
| sta_wf_nil : sta_wf nil
| sta_wf_cons Γ A s :
  sta_wf Γ ->
  Γ ⊢ A : Sort s ->
  sta_wf (A :: Γ).

Scheme sta_type_mut := Induction for sta_type Sort Prop
with sta_wf_mut := Induction for sta_wf Sort Prop.

Lemma sta_type_wf Γ m A : Γ ⊢ m : A -> sta_wf Γ.
Proof with eauto.
  elim=>{Γ m A}...
  { move=>Γ A _ _ _ _ wf. inv wf... }
  { move=>Γ A _ _ _ _ wf. inv wf... }
  { move=>Γ A _ _ _ _ wf. inv wf... }
  { move=>Γ A _ _ _ _ wf. inv wf... }
Qed.
Hint Resolve sta_type_wf.

Lemma sta_sta0_type Γ m A : Γ ⊢ m : A -> sta0_type Γ m A.
Proof with eauto using sta0_type, sta0_wf.
  move:Γ m A. apply:(@sta_type_mut _ (fun Γ wf => sta0_wf Γ))...
  { move=>Γ A B s t tyB ihB.
    have wf0:=sta0_type_wf ihB. inv wf0.
    apply: sta0_pi0... }
  { move=>Γ A B s t tyB ihB.
    have wf0:=sta0_type_wf ihB. inv wf0.
    apply: sta0_pi1... }
  { move=>Γ A B m s tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_lam0... }
  { move=>Γ A B m s tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_lam1... }
  Unshelve. eauto.
Qed.

Lemma sta0_sta_type Γ m A : sta0_type Γ m A -> Γ ⊢ m : A.
Proof with eauto using sta_type, sta_wf.
  move:Γ m A. apply:(@sta0_type_mut _ (fun Γ wf => sta_wf Γ))...
  Unshelve. eauto.
Qed.
