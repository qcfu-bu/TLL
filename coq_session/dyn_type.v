From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_ctx sta_step sta_type
  dyn_ctx dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ ; Γ ; Δ ⊢ m : A"
  (at level 50, Γ, Δ, m, A at next level).
Inductive dyn_type : dyn_ctx -> sta_ctx -> dyn_ctx -> term -> term -> Prop :=
(* core *)
| dyn_var Θ Γ Δ x s A :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x s A ->
  Θ ; Γ ; Δ ⊢ Var x : A
| dyn_lam0 Θ Γ Δ A B m s :
  Θ ▷ s ->
  Δ ▷ s ->
  Θ ; (A :: Γ) ; _: Δ ⊢ m : B ->
  Θ ; Γ ; Δ ⊢ Lam0 A m s : Pi0 A B s
| dyn_lam1 Θ Γ Δ A B m s t :
  Θ ▷ s ->
  Δ ▷ s ->
  Θ ; (A :: Γ) ; A .{t} Δ ⊢ m : B ->
  Θ ; Γ ; Δ ⊢ Lam1 A m s : Pi1 A B s
| dyn_app0 Θ Γ Δ A B m n s :
  Θ ; Γ ; Δ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Θ ; Γ ; Δ ⊢ App0 m n : B.[n/]
| dyn_app1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ; Γ ; Δ1 ⊢ m : Pi1 A B s ->
  Θ2 ; Γ ; Δ2 ⊢ n : A ->
  Θ ; Γ ; Δ ⊢ App1 m n : B.[n/]
| dyn_pair0 Θ Γ Δ A B m n t :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ⊢ m : A ->
  Θ ; Γ ; Δ ⊢ n : B.[m/] ->
  Θ ; Γ ; Δ ⊢ Pair0 m n t : Sig0 A B t
| dyn_pair1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ Sig1 A B t : Sort t ->
  Θ1 ; Γ ; Δ1 ⊢ m : A ->
  Θ2 ; Γ ; Δ2 ⊢ n : B.[m/] ->
  Θ ; Γ ; Δ ⊢ Pair1 m n t : Sig1 A B t
| dyn_letin0 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Θ1 ; Γ ; Δ1 ⊢ m : Sig0 A B t ->
  Θ2 ; (B :: A :: Γ) ; B .{r} _: Δ2 ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Θ ; Γ ; Δ ⊢ LetIn C m n : C.[m/]
| dyn_letin1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Θ1 ; Γ ; Δ1 ⊢ m : Sig1 A B t ->
  Θ2 ; (B :: A :: Γ) ; B .{r2} A .{r1} Δ2 ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Θ ; Γ ; Δ ⊢ LetIn C m n : C.[m/]
| dyn_fix Θ Γ Δ A m :
  Θ ▷ U ->
  Δ ▷ U ->
  Θ ; (A :: Γ) ; A :U Δ ⊢ m : A.[ren (+1)] ->
  Θ ; Γ ; Δ ⊢ Fix A m : A
(* data *)
| dyn_ii Θ Γ Δ :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Θ ; Γ ; Δ ⊢ II : Unit
| dyn_tt Θ Γ Δ :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Θ ; Γ ; Δ ⊢ TT : Bool
| dyn_ff Θ Γ Δ :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Θ ; Γ ; Δ ⊢ FF : Bool
| dyn_ifte Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Bool :: Γ) ⊢ A : Sort s ->
  Θ1 ; Γ ; Δ1 ⊢ m : Bool ->
  Θ2 ; Γ ; Δ2 ⊢ n1 : A.[TT/] ->
  Θ2 ; Γ ; Δ2 ⊢ n2 : A.[FF/] ->
  Θ ; Γ ; Δ ⊢ Ifte A m n1 n2 : A.[m/]
(* monadic *)
| dyn_return Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m : A ->
  Θ ; Γ ; Δ ⊢ Return m : IO A
| dyn_bind Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ B : Sort t ->
  Θ1 ; Γ ; Δ1 ⊢ m : IO A ->
  Θ2 ; (A :: Γ) ; (A .{s} Δ2) ⊢ n : IO B.[ren (+1)] ->
  Θ ; Γ ; Δ ⊢ Bind m n : IO B
(* session *)
| dyn_cvar Θ Γ Δ r x A :
  dyn_just Θ x (Ch r A) ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  nil ⊢ A : Proto ->
  Θ ; Γ ; Δ ⊢ CVar x : Ch r A.[ren (+size Γ)]
| dyn_fork Θ Γ Δ m A :
  Θ ; (Ch true A :: Γ) ; Ch true A :L Δ ⊢ m : IO Unit ->
  Θ ; Γ ; Δ ⊢ Fork A m : IO (Ch false A)
| dyn_recv0 Θ Γ Δ r1 r2 A B m :
  r1 (+) r2 = false ->
  Θ ; Γ ; Δ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Recv0 m : IO (Sig0 A (Ch r1 B) L)
| dyn_recv1 Θ Γ Δ r1 r2 A B m :
  r1 (+) r2 = false ->
  Θ ; Γ ; Δ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Recv1 m : IO (Sig1 A (Ch r1 B) L)
| dyn_send0 Θ Γ Δ r1 r2 A B m :
  r1 (+) r2 = true ->
  Θ ; Γ ; Δ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Send0 m : Pi0 A (IO (Ch r1 B)) L
| dyn_send1 Θ Γ Δ r1 r2 A B m :
  r1 (+) r2 = true ->
  Θ ; Γ ; Δ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Send1 m : Pi1 A (IO (Ch r1 B)) L
| dyn_wait Θ Γ Δ m :
  Θ ; Γ ; Δ ⊢ m : Ch false Stop ->
  Θ ; Γ ; Δ ⊢ Wait m : IO Unit
| dyn_close Θ Γ Δ m :
  Θ ; Γ ; Δ ⊢ m : Ch true Stop ->
  Θ ; Γ ; Δ ⊢ Close m : IO Unit
(* conversion *)
| dyn_conv Θ Γ Δ A B m s :
  A === B ->
  Θ ; Γ ; Δ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  Θ ; Γ ; Δ ⊢ m : B
where "Θ ; Γ ; Δ ⊢ m : A" := (dyn_type Θ Γ Δ m A)

with dyn_wf : sta_ctx -> dyn_ctx -> Prop :=
| dyn_wf_nil : dyn_wf nil nil
| dyn_wf_ty Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn_wf (A :: Γ) (A .{s} Δ)
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

Lemma dyn_type_wf Θ Γ Δ m A : Θ ; Γ ; Δ ⊢ m : A -> dyn_wf Γ Δ.
Proof with eauto 8 using dyn_wf.
  elim=>{Θ Γ Δ m A}...
  { move=>Θ Γ Δ A B m s k1 k2 tym wf. inv wf... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym wf. inv wf... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym wf1 tyn wf2.
    apply: dyn_wf_merge... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym wf1 tyn wf2.
    apply: dyn_wf_merge... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym wf1 wf2 wf.
    inv wf. inv H2. apply: dyn_wf_merge... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym wf1 tyn wf2.
    inv wf2. inv H2. apply: dyn_wf_merge... }
  { move=>Θ Γ Δ A m k1 k2 tym wf. inv wf... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym wf1 tyn1 wf2 tyn2 _.
    apply: dyn_wf_merge... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym wf1 tyn wf2.
    inv wf2. apply: dyn_wf_merge... }
  { move=>Θ Γ Δ m A tym wf. inv wf... }
Qed.
#[global] Hint Resolve dyn_type_wf.

Lemma dyn_sta_wf Γ Δ : dyn_wf Γ Δ -> sta_wf Γ.
Proof with eauto using sta_wf. elim... Qed.

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
