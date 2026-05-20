(** * Logical typing

    Two equivalent presentations of the logical typing judgment. The
    stratified [logical0_type] threads the universe level (and the
    sort of [A] under a Π/Σ) through every binder rule; the surface
    [logical_type] with notation [Γ ⊢ m : A] hides those levels but
    keeps the conversion rule. The two are shown equivalent
    ([logical_logical0_type] / [logical0_logical_type]); the
    stratified form is convenient for SR-style inductions that need
    the level information at each constructor. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_ctx logical_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive logical0_type : logical_ctx -> term -> term -> Prop :=
| logical0_axiom Γ s l :
  logical0_wf Γ ->
  logical0_type Γ (Sort s l) (Sort U l.+1)
| logical0_var Γ x A :
  logical0_wf Γ ->
  logical_has Γ x A ->
  logical0_type Γ (Var x) A
| logical0_pi0 Γ A B s r t l1 l2 :
  logical0_type Γ A (Sort r l1) ->
  logical0_type (A :: Γ) B (Sort t l2) ->
  logical0_type Γ (Pi0 A B s) (Sort s (maxn l1 l2))
| logical0_pi1 Γ A B s r t l1 l2 :
  logical0_type Γ A (Sort r l1) ->
  logical0_type (A :: Γ) B (Sort t l2) ->
  logical0_type Γ (Pi1 A B s) (Sort s (maxn l1 l2))
| logical0_lam0 Γ A B m s r l :
  logical0_type Γ A (Sort r l) ->
  logical0_type (A :: Γ) m B ->
  logical0_type Γ (Lam0 A m s) (Pi0 A B s)
| logical0_lam1 Γ A B m s r l :
  logical0_type Γ A (Sort r l) ->
  logical0_type (A :: Γ) m B ->
  logical0_type Γ (Lam1 A m s) (Pi1 A B s)
| logical0_app0 Γ A B m n s :
  logical0_type Γ m (Pi0 A B s) ->
  logical0_type Γ n A ->
  logical0_type Γ (App m n) B.[n/]
| logical0_app1 Γ A B m n s :
  logical0_type Γ m (Pi1 A B s) ->
  logical0_type Γ n A ->
  logical0_type Γ (App m n) B.[n/]
| logical0_sig0 Γ A B s r t l1 l2 :
  s ⊑ t ->
  logical0_type Γ A (Sort s l1) ->
  logical0_type (A :: Γ) B (Sort r l2) ->
  logical0_type Γ (Sig0 A B t) (Sort t (maxn l1 l2))
| logical0_sig1 Γ A B s r t l1 l2 :
  s ⊑ t ->
  r ⊑ t ->
  logical0_type Γ A (Sort s l1) ->
  logical0_type (A :: Γ) B (Sort r l2) ->
  logical0_type Γ (Sig1 A B t) (Sort t (maxn l1 l2))
| logical0_pair0 Γ A B m n t l :
  logical0_type Γ (Sig0 A B t) (Sort t l) ->
  logical0_type Γ m A ->
  logical0_type Γ n B.[m/] ->
  logical0_type Γ (Pair0 m n t) (Sig0 A B t)
| logical0_pair1 Γ A B m n t l :
  logical0_type Γ (Sig1 A B t) (Sort t l) ->
  logical0_type Γ m A ->
  logical0_type Γ n B.[m/] ->
  logical0_type Γ (Pair1 m n t) (Sig1 A B t)
| logical0_letin0 Γ A B C m n s t l :
  logical0_type (Sig0 A B t :: Γ) C (Sort s l) ->
  logical0_type Γ m (Sig0 A B t) ->
  logical0_type (B :: A :: Γ) n C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  logical0_type Γ (LetIn C m n) C.[m/]
| logical0_letin1 Γ A B C m n s t l :
  logical0_type (Sig1 A B t :: Γ) C (Sort s l) ->
  logical0_type Γ m (Sig1 A B t) ->
  logical0_type (B :: A :: Γ) n C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  logical0_type Γ (LetIn C m n) C.[m/]
| logical0_bool Γ :
  logical0_wf Γ ->
  logical0_type Γ Bool (Sort U 0)
| logical0_tt Γ :
  logical0_wf Γ ->
  logical0_type Γ TT Bool
| logical0_ff Γ :
  logical0_wf Γ ->
  logical0_type Γ FF Bool
| logical0_ifte Γ A m n1 n2 s l :
  logical0_type (Bool :: Γ) A (Sort s l) ->
  logical0_type Γ m Bool ->
  logical0_type Γ n1 A.[TT/] ->
  logical0_type Γ n2 A.[FF/] ->
  logical0_type Γ (Ifte A m n1 n2) A.[m/]
| logical0_id Γ A m n s l :
  logical0_type Γ A (Sort s l) ->
  logical0_type Γ m A ->
  logical0_type Γ n A ->
  logical0_type Γ (Id A m n) (Sort U l)
| logical0_refl Γ A m :
  logical0_type Γ m A ->
  logical0_type Γ (Refl m) (Id A m m)
| logical0_rw Γ A B H P m n s l :
  logical0_type (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) B (Sort s l) ->
  logical0_type Γ H B.[Refl m,m/] ->
  logical0_type Γ P (Id A m n) ->
  logical0_type Γ (Rw B H P) B.[P,n/]
| logical0_conv Γ A B m s l :
  A ≃ B ->
  logical0_type Γ m A ->
  logical0_type Γ B (Sort s l) ->
  logical0_type Γ m B

with logical0_wf : logical_ctx -> Prop :=
| logical0_wf_nil : logical0_wf nil
| logical0_wf_cons Γ A s l :
  logical0_wf Γ ->
  logical0_type Γ A (Sort s l) ->
  logical0_wf (A :: Γ).

Scheme logical0_type_mut := Induction for logical0_type Sort Prop
with logical0_wf_mut := Induction for logical0_wf Sort Prop.

Lemma logical0_type_wf Γ m A : logical0_type Γ m A -> logical0_wf Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
#[global] Hint Resolve logical0_type_wf.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive logical_type : logical_ctx -> term -> term -> Prop :=
| logical_axiom Γ s l :
  logical_wf Γ ->
  Γ ⊢ Sort s l : Sort U l.+1
| logical_var Γ x A :
  logical_wf Γ ->
  logical_has Γ x A ->
  Γ ⊢ Var x : A
| logical_pi0 Γ A B s r t l1 l2 :
  Γ ⊢ A : Sort r l1 ->
  (A :: Γ) ⊢ B : Sort t l2 ->
  Γ ⊢ Pi0 A B s : Sort s (maxn l1 l2)
| logical_pi1 Γ A B s r t l1 l2 :
  Γ ⊢ A : Sort r l1 ->
  (A :: Γ) ⊢ B : Sort t l2 ->
  Γ ⊢ Pi1 A B s : Sort s (maxn l1 l2)
| logical_lam0 Γ A B m s :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam0 A m s : Pi0 A B s
| logical_lam1 Γ A B m s :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam1 A m s : Pi1 A B s
| logical_app0 Γ A B m n s :
  Γ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| logical_app1 Γ A B m n s :
  Γ ⊢ m : Pi1 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| logical_sig0 Γ A B s r t l1 l2 :
  s ⊑ t ->
  Γ ⊢ A : Sort s l1 ->
  (A :: Γ) ⊢ B : Sort r l2 ->
  Γ ⊢ Sig0 A B t : Sort t (maxn l1 l2)
| logical_sig1 Γ A B s r t l1 l2 :
  s ⊑ t ->
  r ⊑ t ->
  Γ ⊢ A : Sort s l1 ->
  (A :: Γ) ⊢ B : Sort r l2 ->
  Γ ⊢ Sig1 A B t : Sort t (maxn l1 l2)
| logical_pair0 Γ A B m n t l :
  Γ ⊢ Sig0 A B t : Sort t l ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair0 m n t : Sig0 A B t
| logical_pair1 Γ A B m n t l :
  Γ ⊢ Sig1 A B t : Sort t l ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair1 m n t : Sig1 A B t
| logical_letin0 Γ A B C m n s t l :
  (Sig0 A B t :: Γ) ⊢ C : Sort s l ->
  Γ ⊢ m : Sig0 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| logical_letin1 Γ A B C m n s t l :
  (Sig1 A B t :: Γ) ⊢ C : Sort s l ->
  Γ ⊢ m : Sig1 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| logical_bool Γ :
  logical_wf Γ ->
  Γ ⊢ Bool : Sort U 0
| logical_tt Γ :
  logical_wf Γ ->
  Γ ⊢ TT : Bool
| logical_ff Γ :
  logical_wf Γ ->
  Γ ⊢ FF : Bool
| logical_ifte Γ A m n1 n2 s l :
  (Bool :: Γ) ⊢ A : Sort s l ->
  Γ ⊢ m : Bool ->
  Γ ⊢ n1 : A.[TT/] ->
  Γ ⊢ n2 : A.[FF/] ->
  Γ ⊢ Ifte A m n1 n2 : A.[m/]
| logical_id Γ A m n s l :
  Γ ⊢ A : Sort s l ->
  Γ ⊢ m : A ->
  Γ ⊢ n : A ->
  Γ ⊢ Id A m n : Sort U l
| logical_refl Γ A m :
  Γ ⊢ m : A ->
  Γ ⊢ Refl m : Id A m m
| logical_rw Γ A B H P m n s l :
  (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) ⊢ B : Sort s l ->
  Γ ⊢ H : B.[Refl m,m/] ->
  Γ ⊢ P : Id A m n ->
  Γ ⊢ Rw B H P : B.[P,n/]
| logical_conv Γ A B m s l :
  A ≃ B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Sort s l ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (logical_type Γ m A)

with logical_wf : logical_ctx -> Prop :=
| logical_wf_nil : logical_wf nil
| logical_wf_cons Γ A s l :
  logical_wf Γ ->
  Γ ⊢ A : Sort s l ->
  logical_wf (A :: Γ).

Scheme logical_type_mut := Induction for logical_type Sort Prop
with logical_wf_mut := Induction for logical_wf Sort Prop.

Lemma logical_type_wf Γ m A : Γ ⊢ m : A -> logical_wf Γ.
Proof with eauto.
  elim=>{Γ m A}...
  { move=>Γ A _ _ _ _ wf. inv wf... }
  { move=>Γ A _ _ _ _ wf. inv wf... }
Qed.
#[global] Hint Resolve logical_type_wf.

Lemma logical_logical0_type Γ m A : Γ ⊢ m : A -> logical0_type Γ m A.
Proof with eauto using logical0_type, logical0_wf.
  move:Γ m A. apply:(@logical_type_mut _ (fun Γ wf => logical0_wf Γ))...
  { move=>Γ A B m s tym ihm.
    have wf0:=logical0_type_wf ihm. inv wf0.
    apply: logical0_lam0... }
  { move=>Γ A B m s tym ihm.
    have wf0:=logical0_type_wf ihm. inv wf0.
    apply: logical0_lam1... }
Qed.
#[global] Hint Resolve logical_logical0_type.

Lemma logical0_logical_type Γ m A : logical0_type Γ m A -> Γ ⊢ m : A.
Proof with eauto using logical_type, logical_wf.
  move:Γ m A. apply:(@logical0_type_mut _ (fun Γ wf => logical_wf Γ))...
Qed.
