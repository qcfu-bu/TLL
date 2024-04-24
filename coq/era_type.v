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
  (A :: Γ) ; A .{t} Δ ⊢ m ~ m' : B ->
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
| era_pair0 Γ Δ A B m m' n t l :
  Γ ⊢ Sig0 A B t : Sort t l ->
  Γ ; Δ ⊢ m ~ m' : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ; Δ ⊢ Pair0 m n t ~ Pair0 m' Box t : Sig0 A B t
| era_pair1 Γ Δ1 Δ2 Δ A B m m' n n' t l :
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ Sig1 A B t : Sort t l ->
  Γ ; Δ1 ⊢ m ~ m' : A ->
  Γ ; Δ2 ⊢ n ~ n' : B.[m/] ->
  Γ ; Δ ⊢ Pair1 m n t ~ Pair1 m' n' t : Sig1 A B t
| era_letin0 Γ Δ1 Δ2 Δ A B C m m' n n' s r t l :
  Δ1 ∘ Δ2 => Δ ->
  (Sig0 A B t :: Γ) ⊢ C : Sort s l ->
  Γ ; Δ1 ⊢ m ~ m' : Sig0 A B t ->
  (B :: A :: Γ) ; _: A .{r} Δ2 ⊢ n ~ n' : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ; Δ ⊢ LetIn C m n ~ LetIn Box m' n' : C.[m/]
| era_letin1 Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t l :
  Δ1 ∘ Δ2 => Δ ->
  (Sig1 A B t :: Γ) ⊢ C : Sort s l ->
  Γ ; Δ1 ⊢ m ~ m' : Sig1 A B t ->
  (B :: A :: Γ) ; B .{r2} A .{r1} Δ2 ⊢ n ~ n' : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ; Δ ⊢ LetIn C m n ~ LetIn Box m' n' : C.[m/]
| era_tt Γ Δ :
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Γ ; Δ ⊢ TT ~ TT : Bool
| era_ff Γ Δ :
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Γ ; Δ ⊢ FF ~ FF : Bool
| era_ifte Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s l :
  Δ1 ∘ Δ2 => Δ ->
  (Bool :: Γ) ⊢ A : Sort s l ->
  Γ ; Δ1 ⊢ m ~ m' : Bool ->
  Γ ; Δ2 ⊢ n1 ~ n1' : A.[TT/] ->
  Γ ; Δ2 ⊢ n2 ~ n2' : A.[FF/] ->
  Γ ; Δ ⊢ Ifte A m n1 n2 ~ Ifte Box m' n1' n2' : A.[m/]
| era_rw Γ Δ A B H H' P m n s l :
  (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) ⊢ B : Sort s l ->
  Γ ; Δ ⊢ H ~ H' : B.[Refl m,m/] ->
  Γ ⊢ P : Id A m n ->
  Γ ; Δ ⊢ Rw B H P ~ Rw Box H' Box : B.[P,n/]
| era_conv Γ Δ A B m m' s l :
  A ≃ B ->
  Γ ; Δ ⊢ m ~ m' : A ->
  Γ ⊢ B : Sort s l ->
  Γ ; Δ ⊢ m ~ m' : B
where "Γ ; Δ ⊢ m ~ n : A" := (era_type Γ Δ m n A).

Lemma era_dyn_type Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_type. elim... Qed.
#[global] Hint Resolve era_dyn_type.

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
    exists (App m' Box)... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym[m' erm]tyn[n' ern].
    exists (App m' n')... }
  { move=>Γ Δ A B m n t l tyS tym[m' tym']tyn.
    exists (Pair0 m' Box t)... }
  { move=>Γ Δ1 Δ2 Δ A B m n t l mrg tyS tym[m' tym']tyn[n' tyn'].
    exists (Pair1 m' n' t)... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t l mrg tyC tym[m' tym']tyn[n' tyn'].
    exists (LetIn Box m' n')... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t l mrg tyC tym[m' tym']tyn[n' tyn'].
    exists (LetIn Box m' n')... }
  { move=>Γ Δ wf k. exists TT... }
  { move=>Γ Δ wf k. exists FF... }
  { move=>Γ Δ1 Δ2 Δ A m n1 n2 s l mrg tyA tym[m' ihm']tyn1[n1' ihn1']tyn2[n2' ihn2'].
    exists (Ifte Box m' n1' n2')... }
  { move=>Γ Δ A B H P m n s l tyB tyH[H' erH]tyP.
    exists (Rw Box H' Box).
    apply: era_rw... }
  { move=>Γ Δ A B m s l eq tym[m' er]tyB.
    exists m'. apply: era_conv... }
Qed.
