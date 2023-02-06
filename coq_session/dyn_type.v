From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_ctx sta_step sta_type
  dyn_ctx dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ; Δ ; Θ ⊢ m : A"
  (at level 50, Δ, Θ, m, A at next level).
Inductive dyn_type : sta_ctx -> dyn_ctx -> dyn_ctx -> term -> term -> Prop :=
(* core *)
| dyn_var Γ Δ Θ x s A :
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x s A ->
  dyn_empty Θ ->
  Γ ; Δ ; Θ ⊢ Var x : A
| dyn_lam0 Γ Δ Θ A B m s :
  Δ ▷ s ->
  Θ ▷ s ->
  (A :: Γ) ; _: Δ ; Θ ⊢ m : B ->
  Γ ; Δ ; Θ ⊢ Lam0 A m s : Pi0 A B s
| dyn_lam1 Γ Δ Θ A B m s t :
  Δ ▷ s ->
  Θ ▷ s ->
  (A :: Γ) ; A :{t} Δ ; Θ ⊢ m : B ->
  Γ ; Δ ; Θ ⊢ Lam1 A m s : Pi1 A B s
| dyn_app0 Γ Δ Θ A B m n s :
  Γ ; Δ ; Θ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ; Δ ; Θ ⊢ App m n : B.[n/]
| dyn_app1 Γ Δ1 Δ2 Δ Θ1 Θ2 Θ A B m n s :
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ∘ Θ2 => Θ ->
  Γ ; Δ1 ; Θ1 ⊢ m : Pi1 A B s ->
  Γ ; Δ2 ; Θ2 ⊢ n : A ->
  Γ ; Δ ; Θ ⊢ App m n : B.[n/]
| dyn_pair0 Γ Δ Θ A B m n t :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ; Δ ; Θ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ; Δ ; Θ ⊢ Pair0 m n t : Sig0 A B t
| dyn_pair1 Γ Δ1 Δ2 Δ Θ1 Θ2 Θ A B m n t :
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ∘ Θ2 => Θ ->
  Γ ⊢ Sig1 A B t : Sort t ->
  Γ ; Δ1 ; Θ1 ⊢ m : A ->
  Γ ; Δ2 ; Θ2 ⊢ n : B.[m/] ->
  Γ ; Δ ; Θ ⊢ Pair1 m n t : Sig1 A B t
| dyn_letin0 Γ Δ1 Δ2 Δ Θ1 Θ2 Θ A B C m n s r t :
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ∘ Θ2 => Θ ->
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Γ ; Δ1 ; Θ1 ⊢ m : Sig0 A B t ->
  (B :: A :: Γ) ; _: A :{r} Δ2 ; Θ2 ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ; Δ ; Θ ⊢ LetIn C m n : C.[m/]
| dyn_letin1 Γ Δ1 Δ2 Δ Θ1 Θ2 Θ A B C m n s r1 r2 t :
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ∘ Θ2 => Θ ->
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Γ ; Δ1 ; Θ1 ⊢ m : Sig1 A B t ->
  (B :: A :: Γ) ; B :{r2} A :{r1} Δ2 ; Θ2 ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ; Δ ; Θ ⊢ LetIn C m n : C.[m/]
| dyn_sta_fix Γ Δ Θ A m :
  Δ ▷ U ->
  Θ ▷ U ->
  (A :: Γ) ; A :U Δ ; Θ ⊢ m : A.[ren (+1)] ->
  Γ ; Δ ; Θ ⊢ Fix A m : A
(* data *)
| dyn_ii Γ Δ Θ :
  Δ ▷ U ->
  dyn_wf Γ Δ ->
  dyn_empty Θ ->
  Γ ; Δ ; Θ ⊢ II : Unit
| dyn_tt Γ Δ Θ :
  Δ ▷ U ->
  dyn_wf Γ Δ ->
  dyn_empty Θ ->
  Γ ; Δ ; Θ ⊢ TT : Bool
| dyn_ff Γ Δ Θ :
  Δ ▷ U ->
  dyn_wf Γ Δ ->
  dyn_empty Θ ->
  Γ ; Δ ; Θ ⊢ FF : Bool
| dyn_ifte Γ Δ1 Δ2 Δ Θ1 Θ2 Θ A m n1 n2 s :
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ∘ Θ2 => Θ ->
  Γ ; Δ1 ; Θ1 ⊢ m : Bool ->
  (Bool :: Γ) ⊢ A : Sort s ->
  Γ ; Δ2 ; Θ2 ⊢ n1 : A.[TT/] ->
  Γ ; Δ2 ; Θ2 ⊢ n2 : A.[FF/] ->
  Γ ; Δ ; Θ ⊢ Ifte A m n1 n2 : A.[m/]
(* monadic *)
| dyn_return Γ Δ Θ m A :
  Γ ; Δ ; Θ ⊢ m : A ->
  Γ ; Δ ; Θ ⊢ Return m : IO A
| dyn_bind Γ Δ1 Δ2 Δ Θ1 Θ2 Θ m n A B s t :
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ∘ Θ2 => Θ ->
  Γ ⊢ B : Sort t ->
  Γ ; Δ1 ; Θ1 ⊢ m : IO A ->
  (A :: Γ) ; (A :{s} Δ2) ; Θ2 ⊢ n : IO B.[ren (+1)] ->
  Γ ; Δ ; Θ ⊢ Bind m n : IO B
(* session *)
| dyn_cvar Γ Δ Θ r x A :
  Δ ▷ U ->
  Γ ⊢ A : Proto ->
  dyn_just Θ x (Ch r A) ->
  Γ ; Δ ; Θ ⊢ CVar x : Ch r A
| dyn_fork Γ Δ Θ m A :
  (Ch true A :: Γ) ; Ch true A :L Δ ; Θ ⊢ m : IO Unit ->
  Γ ; Δ ; Θ ⊢ Fork A m : IO (Ch false A)
| dyn_recv0 Γ Δ Θ r1 r2 A B m :
  r1 (+) r2 = false ->
  Γ ; Δ ; Θ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Γ ; Δ ; Θ ⊢ Recv m : IO (Sig0 A (Ch r1 B) L)
| dyn_recv1 Γ Δ Θ r1 r2 A B m :
  r1 (+) r2 = false ->
  Γ ; Δ ; Θ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Γ ; Δ ; Θ ⊢ Recv m : IO (Sig1 A (Ch r1 B) L)
| dyn_send0 Γ Δ Θ r1 r2 A B m :
  r1 (+) r2 = true ->
  Γ ; Δ ; Θ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Γ ; Δ ; Θ ⊢ Send m : Pi0 A (IO (Ch r1 B)) L
| dyn_send1 Γ Δ Θ r1 r2 A B m :
  r1 (+) r2 = true ->
  Γ ; Δ ; Θ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Γ ; Δ ; Θ ⊢ Send m : Pi1 A (IO (Ch r1 B)) L
| dyn_wait Γ Δ Θ r1 r2 m :
  r1 (+) r2 = false ->
  Γ ; Δ ; Θ ⊢ m : Ch r1 (Stop r2) ->
  Γ ; Δ ; Θ ⊢ Wait m : IO Unit
| dyn_close Γ Δ Θ r1 r2 m :
  r1 (+) r2 = true ->
  Γ ; Δ ; Θ ⊢ m : Ch r1 (Stop r2) ->
  Γ ; Δ ; Θ ⊢ Close m : IO Unit
(* conversion *)
| dyn_conv Γ Δ Θ A B m s :
  A === B ->
  Γ ; Δ ; Θ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  Γ ; Δ ; Θ ⊢ m : B
where "Γ ; Δ ; Θ ⊢ m : A" := (dyn_type Γ Δ Θ m A)

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

Lemma dyn_type_wf Γ Δ Θ m A : Γ ; Δ ; Θ ⊢ m : A -> dyn_wf Γ Δ.
Proof with eauto 8 using dyn_wf.
  elim=>{Γ Δ Θ m A}...
  { move=>Γ Δ Θ A B m s k1 k2 tym ih. inv ih... }
  { move=>Γ Δ Θ A B m s t k1 k2 tym ih. inv ih... }
  { move=>Γ Δ1 Δ2 Δ Θ1 Θ2 Θ A B m n s mrg tym ihm tyn ihn.
    apply: dyn_wf_merge... }
Qed.
Hint Resolve dyn_type_wf.

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
