From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta0_type : sta_ctx -> term -> term -> Prop :=
| sta0_axiom Γ s l :
  sta0_wf Γ ->
  sta0_type Γ (Sort s l) (Sort U l.+1)
| sta0_var Γ x A :
  sta0_wf Γ ->
  sta_has Γ x A ->
  sta0_type Γ (Var x) A
| sta0_pi0 Γ A B s r t l1 l2 :
  sta0_type Γ A (Sort r l1) ->
  sta0_type (A :: Γ) B (Sort t l2) ->
  sta0_type Γ (Pi0 A B s) (Sort s (maxn l1 l2))
| sta0_pi1 Γ A B s r t l1 l2 :
  sta0_type Γ A (Sort r l1) ->
  sta0_type (A :: Γ) B (Sort t l2) ->
  sta0_type Γ (Pi1 A B s) (Sort s (maxn l1 l2))
| sta0_lam0 Γ A B m s r l :
  sta0_type Γ A (Sort r l) ->
  sta0_type (A :: Γ) m B ->
  sta0_type Γ (Lam0 A m s) (Pi0 A B s)
| sta0_lam1 Γ A B m s r l :
  sta0_type Γ A (Sort r l) ->
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
| sta0_sig0 Γ A B s r t l1 l2 :
  s ⊑ t ->
  sta0_type Γ A (Sort s l1) ->
  sta0_type (A :: Γ) B (Sort r l2) ->
  sta0_type Γ (Sig0 A B t) (Sort t (maxn l1 l2))
| sta0_sig1 Γ A B s r t l1 l2 :
  s ⊑ t ->
  r ⊑ t ->
  sta0_type Γ A (Sort s l1) ->
  sta0_type (A :: Γ) B (Sort r l2) ->
  sta0_type Γ (Sig1 A B t) (Sort t (maxn l1 l2))
| sta0_pair0 Γ A B m n t l :
  sta0_type Γ (Sig0 A B t) (Sort t l) ->
  sta0_type Γ m A ->
  sta0_type Γ n B.[m/] ->
  sta0_type Γ (Pair0 m n t) (Sig0 A B t)
| sta0_pair1 Γ A B m n t l :
  sta0_type Γ (Sig1 A B t) (Sort t l) ->
  sta0_type Γ m A ->
  sta0_type Γ n B.[m/] ->
  sta0_type Γ (Pair1 m n t) (Sig1 A B t)
| sta0_letin0 Γ A B C m n s t l :
  sta0_type (Sig0 A B t :: Γ) C (Sort s l) ->
  sta0_type Γ m (Sig0 A B t) ->
  sta0_type (B :: A :: Γ) n C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  sta0_type Γ (LetIn C m n) C.[m/]
| sta0_letin1 Γ A B C m n s t l :
  sta0_type (Sig1 A B t :: Γ) C (Sort s l) ->
  sta0_type Γ m (Sig1 A B t) ->
  sta0_type (B :: A :: Γ) n C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  sta0_type Γ (LetIn C m n) C.[m/]
| sta0_with Γ A B s r t l1 l2 :
  sta0_type Γ A (Sort s l1) ->
  sta0_type Γ B (Sort r l2) ->
  sta0_type Γ (With A B t) (Sort t (maxn l1 l2))
| sta0_apair Γ A B m n t :
  sta0_type Γ m A ->
  sta0_type Γ n B ->
  sta0_type Γ (APair m n t) (With A B t)
| sta0_fst Γ A B m t :
  sta0_type Γ m (With A B t) ->
  sta0_type Γ (Fst m) A
| sta0_snd Γ A B m t :
  sta0_type Γ m (With A B t) ->
  sta0_type Γ (Snd m) B
| sta0_id Γ A m n s l :
  sta0_type Γ A (Sort s l) ->
  sta0_type Γ m A ->
  sta0_type Γ n A ->
  sta0_type Γ (Id A m n) (Sort U l)
| sta0_refl Γ A m :
  sta0_type Γ m A ->
  sta0_type Γ (Refl m) (Id A m m)
| sta0_rw Γ A B H P m n s l :
  sta0_type (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) B (Sort s l) ->
  sta0_type Γ H B.[Refl m,m/] ->
  sta0_type Γ P (Id A m n) ->
  sta0_type Γ (Rw B H P) B.[P,n/]
| sta0_conv Γ A B m s l :
  A === B ->
  sta0_type Γ m A ->
  sta0_type Γ B (Sort s l) ->
  sta0_type Γ m B

with sta0_wf : sta_ctx -> Prop :=
| sta0_wf_nil : sta0_wf nil
| sta0_wf_cons Γ A s l :
  sta0_wf Γ ->
  sta0_type Γ A (Sort s l) ->
  sta0_wf (A :: Γ).

Scheme sta0_type_mut := Induction for sta0_type Sort Prop
with sta0_wf_mut := Induction for sta0_wf Sort Prop.

Lemma sta0_type_wf Γ m A : sta0_type Γ m A -> sta0_wf Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
#[global] Hint Resolve sta0_type_wf.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive sta_type : sta_ctx -> term -> term -> Prop :=
| sta_axiom Γ s l :
  sta_wf Γ ->
  Γ ⊢ Sort s l : Sort U l.+1
| sta_var Γ x A :
  sta_wf Γ ->
  sta_has Γ x A ->
  Γ ⊢ Var x : A
| sta_pi0 Γ A B s r t l1 l2 :
  Γ ⊢ A : Sort r l1 ->
  (A :: Γ) ⊢ B : Sort t l2 ->
  Γ ⊢ Pi0 A B s : Sort s (maxn l1 l2)
| sta_pi1 Γ A B s r t l1 l2 :
  Γ ⊢ A : Sort r l1 ->
  (A :: Γ) ⊢ B : Sort t l2 ->
  Γ ⊢ Pi1 A B s : Sort s (maxn l1 l2)
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
| sta_sig0 Γ A B s r t l1 l2 :
  s ⊑ t ->
  Γ ⊢ A : Sort s l1 ->
  (A :: Γ) ⊢ B : Sort r l2 ->
  Γ ⊢ Sig0 A B t : Sort t (maxn l1 l2)
| sta_sig1 Γ A B s r t l1 l2 :
  s ⊑ t ->
  r ⊑ t ->
  Γ ⊢ A : Sort s l1 ->
  (A :: Γ) ⊢ B : Sort r l2 ->
  Γ ⊢ Sig1 A B t : Sort t (maxn l1 l2)
| sta_pair0 Γ A B m n t l :
  Γ ⊢ Sig0 A B t : Sort t l ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair0 m n t : Sig0 A B t
| sta_pair1 Γ A B m n t l :
  Γ ⊢ Sig1 A B t : Sort t l ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair1 m n t : Sig1 A B t
| sta_letin0 Γ A B C m n s t l :
  (Sig0 A B t :: Γ) ⊢ C : Sort s l ->
  Γ ⊢ m : Sig0 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| sta_letin1 Γ A B C m n s t l :
  (Sig1 A B t :: Γ) ⊢ C : Sort s l ->
  Γ ⊢ m : Sig1 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| sta_with Γ A B s r t l1 l2 :
  Γ ⊢ A : Sort s l1 ->
  Γ ⊢ B : Sort r l2 ->
  Γ ⊢ With A B t : Sort t (maxn l1 l2)
| sta_apair Γ A B m n t :
  Γ ⊢ m : A ->
  Γ ⊢ n : B ->
  Γ ⊢ APair m n t : With A B t
| sta_fst Γ A B m t :
  Γ ⊢ m : With A B t ->
  Γ ⊢ Fst m : A
| sta_snd Γ A B m t :
  Γ ⊢ m : With A B t ->
  Γ ⊢ Snd m : B
| sta_id Γ A m n s l :
  Γ ⊢ A : Sort s l ->
  Γ ⊢ m : A ->
  Γ ⊢ n : A ->
  Γ ⊢ Id A m n : Sort U l
| sta_refl Γ A m :
  Γ ⊢ m : A ->
  Γ ⊢ Refl m : Id A m m
| sta_rw Γ A B H P m n s l :
  (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) ⊢ B : Sort s l ->
  Γ ⊢ H : B.[Refl m,m/] ->
  Γ ⊢ P : Id A m n ->
  Γ ⊢ Rw B H P : B.[P,n/]
| sta_conv Γ A B m s l :
  A === B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Sort s l ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (sta_type Γ m A)

with sta_wf : sta_ctx -> Prop :=
| sta_wf_nil : sta_wf nil
| sta_wf_cons Γ A s l :
  sta_wf Γ ->
  Γ ⊢ A : Sort s l ->
  sta_wf (A :: Γ).

Scheme sta_type_mut := Induction for sta_type Sort Prop
with sta_wf_mut := Induction for sta_wf Sort Prop.

Lemma sta_type_wf Γ m A : Γ ⊢ m : A -> sta_wf Γ.
Proof with eauto.
  elim=>{Γ m A}...
  { move=>Γ A _ _ _ _ wf. inv wf... }
  { move=>Γ A _ _ _ _ wf. inv wf... }
Qed.
#[global] Hint Resolve sta_type_wf.

Lemma sta_sta0_type Γ m A : Γ ⊢ m : A -> sta0_type Γ m A.
Proof with eauto using sta0_type, sta0_wf.
  move:Γ m A. apply:(@sta_type_mut _ (fun Γ wf => sta0_wf Γ))...
  { move=>Γ A B m s tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_lam0... }
  { move=>Γ A B m s tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_lam1... }
  Unshelve. eauto.
  Unshelve. eauto.
Qed.
#[global] Hint Resolve sta_sta0_type.

Lemma sta0_sta_type Γ m A : sta0_type Γ m A -> Γ ⊢ m : A.
Proof with eauto using sta_type, sta_wf.
  move:Γ m A. apply:(@sta0_type_mut _ (fun Γ wf => sta_wf Γ))...
  Unshelve. eauto.
  Unshelve. eauto.
Qed.
