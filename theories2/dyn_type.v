From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_ctx sta_step sta_type
  dyn_ctx dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn0_type : sta_ctx -> dyn_ctx -> term -> term -> Prop :=
| dyn0_var Γ Δ x A :
  dyn0_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x A ->
  dyn0_type Γ Δ (Var x) A
| dyn0_lam0 Γ Δ A B m s r :
  Δ ▷ s ->
  Γ ⊢ A : Sort r ->
  dyn0_type (A :: Γ) (_: Δ) m B ->
  dyn0_type Γ Δ (Lam0 A m s) (Pi0 A B s)
| dyn0_lam1 Γ Δ A B m s r :
  Δ ▷ s ->
  Γ ⊢ A : Sort r ->
  dyn0_type (A :: Γ) (A :{r} Δ) m B ->
  dyn0_type Γ Δ (Lam1 A m s) (Pi1 A B s)
| dyn0_app0 Γ Δ A B m n s :
  dyn0_type Γ Δ m (Pi0 A B s) ->
  Γ ⊢ n : A ->
  dyn0_type Γ Δ (App m n) B.[n/]
| dyn0_app1 Γ Δ1 Δ2 Δ A B m n s :
  Δ1 ∘ Δ2 => Δ ->
  dyn0_type Γ Δ1 m (Pi1 A B s) ->
  dyn0_type Γ Δ2 n A ->
  dyn0_type Γ Δ (App m n) B.[n/]
| dyn0_conv Γ Δ A B m s :
  A === B ->
  dyn0_type Γ Δ m A ->
  Γ ⊢ B : Sort s ->
  dyn0_type Γ Δ m B

with dyn0_wf : sta_ctx -> dyn_ctx -> Prop :=
| dyn0_wf_nil : dyn0_wf nil nil
| dyn0_wf_ty Γ Δ A s :
  dyn0_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn0_wf (A :: Γ) (A :{s} Δ)
| dyn0_wf_n Γ Δ A s :
  dyn0_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn0_wf (A :: Γ) (_: Δ).

Scheme dyn0_type_mut := Induction for dyn0_type Sort Prop
with dyn0_wf_mut := Induction for dyn0_wf Sort Prop.

Lemma dyn0_wf_merge Γ Δ Δ1 Δ2 :
  Δ1 ∘ Δ2 => Δ -> dyn0_wf Γ Δ1 -> dyn0_wf Γ Δ2 -> dyn0_wf Γ Δ.
Proof with eauto using dyn0_wf.
  move=>mrg wf.  elim: wf Δ Δ2 mrg=>{Γ Δ1}.
  { move=>Δ Δ2 mrg wf. inv mrg... }
  { move=>Γ Δ1 A s wf1 ih tyA Δ Δ2 mrg wf2. inv mrg.
    { inv wf2. apply: dyn0_wf_ty... }
    { inv wf2. apply: dyn0_wf_ty... } }
  { move=>Γ Δ1 A s wf1 ih tyA Δ Δ2 mrg wf2. inv mrg.
    { inv wf2. apply: dyn0_wf_ty... }
    { inv wf2. apply: dyn0_wf_n... } }
Qed.

Lemma dyn0_type_wf Γ Δ m A : dyn0_type Γ Δ m A -> dyn0_wf Γ Δ.
Proof with eauto using dyn0_wf.
  elim=>{Γ Δ m A}...
  { move=>Γ Δ A B m s r k tyA tym ih. inv ih... }
  { move=>Γ Δ A B m s r k tyA tym ih. inv ih... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn.
    apply: dyn0_wf_merge... }
Qed.
Hint Resolve dyn0_type_wf.

Reserved Notation "Γ ; Δ ⊢ m : A" (at level 50, Δ, m, A at next level).
Inductive dyn_type : sta_ctx -> dyn_ctx -> term -> term -> Prop :=
| dyn_var Γ Δ x A :
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x A ->
  Γ ; Δ ⊢ Var x : A
| dyn_lam0 Γ Δ A B m s :
  Δ ▷ s ->
  (A :: Γ) ; (_: Δ) ⊢ m : B ->
  Γ ; Δ ⊢ Lam0 A m s : Pi0 A B s
| dyn_lam1 Γ Δ A B m s t :
  Δ ▷ s ->
  (A :: Γ) ; (A :{t} Δ) ⊢ m : B ->
  Γ ; Δ ⊢ Lam1 A m s : Pi1 A B s
| dyn_app0 Γ Δ A B m n s :
  Γ ; Δ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ; Δ ⊢ App m n : B.[n/]
| dyn_app1 Γ Δ1 Δ2 Δ A B m n s :
  Δ1 ∘ Δ2 => Δ ->
  Γ ; Δ1 ⊢ m : Pi1 A B s ->
  Γ ; Δ2 ⊢ n : A ->
  Γ ; Δ ⊢ App m n : B.[n/]
| dyn_conv Γ Δ A B m s :
  A === B ->
  Γ ; Δ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m : B
where "Γ ; Δ ⊢ m : A" := (dyn_type Γ Δ m A)

with dyn_wf : sta_ctx -> dyn_ctx -> Prop :=
| dyn_wf_nil : dyn_wf nil nil
| dyn_wf_ty Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn_wf (A :: Γ) (A :{s} Δ)
| dyn_wf_n Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn_wf (A :: Γ) (_: Δ).

Scheme dyn_type_mut := Induction for dyn_type Sort Prop
with dyn_wf_mut := Induction for dyn_wf Sort Prop.

Lemma dyn_wf_merge Γ Δ Δ1 Δ2 :
  Δ1 ∘ Δ2 => Δ -> dyn_wf Γ Δ1 -> dyn_wf Γ Δ2 -> dyn_wf Γ Δ.
Proof with eauto using dyn_wf.
  move=>mrg wf.  elim: wf Δ Δ2 mrg=>{Γ Δ1}.
  { move=>Δ Δ2 mrg wf. inv mrg... }
  { move=>Γ Δ1 A s wf1 ih tyA Δ Δ2 mrg wf2. inv mrg.
    { inv wf2. apply: dyn_wf_ty... }
    { inv wf2. apply: dyn_wf_ty... } }
  { move=>Γ Δ1 A s wf1 ih tyA Δ Δ2 mrg wf2. inv mrg.
    { inv wf2. apply: dyn_wf_ty... }
    { inv wf2. apply: dyn_wf_n... } }
Qed.

Lemma dyn_type_wf Γ Δ m A : Γ ; Δ ⊢ m : A -> dyn_wf Γ Δ.
Proof with eauto using dyn_wf.
  elim=>{Γ Δ m A}...
  { move=>Γ Δ A B m s k tym ih. inv ih... }
  { move=>Γ Δ A B m s t k tym ih. inv ih... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn.
    apply: dyn_wf_merge... }
Qed.
Hint Resolve dyn_type_wf.

Lemma dyn_dyn0_type Γ Δ m A : Γ ; Δ ⊢ m : A -> dyn0_type Γ Δ m A.
Proof with eauto using dyn0_type, dyn0_wf.
  move:Γ Δ m A.
  apply:(@dyn_type_mut _ (fun Γ Δ wf => dyn0_wf Γ Δ))...
  { move=>Γ Δ A B m s k tym ihm.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn0_lam0... }
  { move=>Γ Δ A B m s t k tym ihm.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn0_lam1... }
Qed.

Lemma dyn0_dyn_type Γ Δ m A : dyn0_type Γ Δ m A -> Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_type, dyn_wf.
  move:Γ Δ m A.
  apply:(@dyn0_type_mut _ (fun Γ Δ wf => dyn_wf Γ Δ))...
Qed.

Lemma dyn_wf_inv Γ Δ Δ1 Δ2 :
  Δ1 ∘ Δ2 => Δ -> dyn_wf Γ Δ -> dyn_wf Γ Δ1 /\ dyn_wf Γ Δ2.
Proof with eauto using dyn_wf.
  move=>mrg agr. elim: agr Δ1 Δ2 mrg=>{Γ Δ}.
  { move=>Δ1 Δ2 mrg. inv mrg... }
  { move=>Γ Δ A s wf ih tyA Δ1 Δ2 mrg. inv mrg.
    { have[wf1 wf2]:=ih _ _ H2... }
    { have[wf1 wf2]:=ih _ _ H2... }
    { have[wf1 wf2]:=ih _ _ H2... } }
  { move=>Γ Δ A s wf ih tyA Δ1 Δ2 mrg. inv mrg.
    have[wf1 wf2]:=ih _ _ H2... }
Qed.
