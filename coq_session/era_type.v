From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ ; Γ ; Δ ⊢ m ~ n : A"
  (at level 50, Γ, Δ, m, n, A at next level).

Inductive era_type 
: dyn_ctx -> sta_ctx -> dyn_ctx -> term -> term -> term -> Prop :=
(* core *)
| era_var Θ Γ Δ x s A :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x s A ->
  Θ ; Γ ; Δ ⊢ Var x ~ Var x : A
| era_lam0 Θ Γ Δ A B m m' s :
  Θ ▷ s ->
  Δ ▷ s ->
  Θ ; (A :: Γ) ; _: Δ ⊢ m ~ m' : B ->
  Θ ; Γ ; Δ ⊢ Lam0 A m s ~ Lam0 Box m' s : Pi0 A B s
| era_lam1 Θ Γ Δ A B m m' s t :
  Θ ▷ s ->
  Δ ▷ s ->
  Θ ; (A :: Γ) ; A .{t} Δ ⊢ m ~ m' : B ->
  Θ ; Γ ; Δ ⊢ Lam1 A m s ~ Lam1 Box m' s : Pi1 A B s
| era_app0 Θ Γ Δ A B m m' n s :
  Θ ; Γ ; Δ ⊢ m ~ m' : Pi0 A B s ->
  Γ ⊢ n : A ->
  Θ ; Γ ; Δ ⊢ App0 m n ~ App0 m' Box : B.[n/]
| era_app1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Θ1 ; Γ ; Δ1 ⊢ m ~ m' : Pi1 A B s ->
  Θ2 ; Γ ; Δ2 ⊢ n ~ n' : A ->
  Θ ; Γ ; Δ ⊢ App1 m n ~ App1 m' n' : B.[n/]
| era_pair0 Θ Γ Δ A B m n n' t :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ⊢ m : A ->
  Θ ; Γ ; Δ ⊢ n ~ n' : B.[m/] ->
  Θ ; Γ ; Δ ⊢ Pair0 m n t ~ Pair0 Box n' t : Sig0 A B t
| era_pair1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ Sig1 A B t : Sort t ->
  Θ1 ; Γ ; Δ1 ⊢ m ~ m' : A ->
  Θ2 ; Γ ; Δ2 ⊢ n ~ n' : B.[m/] ->
  Θ ; Γ ; Δ ⊢ Pair1 m n t ~ Pair1 m' n' t : Sig1 A B t
| era_letin0 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Θ1 ; Γ ; Δ1 ⊢ m ~ m' : Sig0 A B t ->
  Θ2 ; (B :: A :: Γ) ; B .{r} _: Δ2 ⊢ n ~ n' : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Θ ; Γ ; Δ ⊢ LetIn C m n ~ LetIn Box m' n' : C.[m/]
| era_letin1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Θ1 ; Γ ; Δ1 ⊢ m ~ m' : Sig1 A B t ->
  Θ2 ; (B :: A :: Γ) ; B .{r2} A .{r1} Δ2 ⊢ n ~ n' : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Θ ; Γ ; Δ ⊢ LetIn C m n ~ LetIn Box m' n' : C.[m/]
(* data *)
| era_ii Θ Γ Δ :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Θ ; Γ ; Δ ⊢ II ~ II : Unit
| era_tt Θ Γ Δ :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Θ ; Γ ; Δ ⊢ TT ~ TT : Bool
| era_ff Θ Γ Δ :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  Θ ; Γ ; Δ ⊢ FF ~ FF : Bool
| era_ifte Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Bool :: Γ) ⊢ A : Sort s ->
  Θ1 ; Γ ; Δ1 ⊢ m ~ m' : Bool ->
  Θ2 ; Γ ; Δ2 ⊢ n1 ~ n1' : A.[TT/] ->
  Θ2 ; Γ ; Δ2 ⊢ n2 ~ n2' : A.[FF/] ->
  Θ ; Γ ; Δ ⊢ Ifte A m n1 n2 ~ Ifte Box m' n1' n2' : A.[m/]
(* monadic *)
| era_return Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A ->
  Θ ; Γ ; Δ ⊢ Return m ~ Return m' : IO A
| era_bind Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ B : Sort t ->
  Θ1 ; Γ ; Δ1 ⊢ m ~ m' : IO A ->
  Θ2 ; (A :: Γ) ; (A .{s} Δ2) ⊢ n ~ n' : IO B.[ren (+1)] ->
  Θ ; Γ ; Δ ⊢ Bind m n ~ Bind m' n' : IO B
(* session *)
| era_cvar Θ Γ Δ r x A :
  dyn_just Θ x (Ch r A) ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  nil ⊢ A : Proto ->
  Θ ; Γ ; Δ ⊢ CVar x ~ CVar x : Ch r A.[ren (+size Γ)]
| era_fork Θ Γ Δ m m' A :
  Θ ; (Ch true A :: Γ) ; Ch true A :L Δ ⊢ m ~ m' : IO Unit ->
  Θ ; Γ ; Δ ⊢ Fork A m ~ Fork Box m' : IO (Ch false A)
| era_recv0 Θ Γ Δ r1 r2 A B m m' :
  r1 (+) r2 = false ->
  Θ ; Γ ; Δ ⊢ m ~ m' : Ch r1 (Act0 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Recv0 m ~ Recv0 m' : IO (Sig0 A (Ch r1 B) L)
| era_recv1 Θ Γ Δ r1 r2 A B m m' :
  r1 (+) r2 = false ->
  Θ ; Γ ; Δ ⊢ m ~ m' : Ch r1 (Act1 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Recv1 m ~ Recv1 m' : IO (Sig1 A (Ch r1 B) L)
| era_send0 Θ Γ Δ r1 r2 A B m m' :
  r1 (+) r2 = true ->
  Θ ; Γ ; Δ ⊢ m ~ m' : Ch r1 (Act0 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Send0 m ~ Send0 m' : Pi0 A (IO (Ch r1 B)) L
| era_send1 Θ Γ Δ r1 r2 A B m m' :
  r1 (+) r2 = true ->
  Θ ; Γ ; Δ ⊢ m ~ m' : Ch r1 (Act1 r2 A B) ->
  Θ ; Γ ; Δ ⊢ Send1 m ~ Send1 m' : Pi1 A (IO (Ch r1 B)) L
| era_wait Θ Γ Δ m m' :
  Θ ; Γ ; Δ ⊢ m ~ m' : Ch false Stop ->
  Θ ; Γ ; Δ ⊢ Wait m ~ Wait m' : IO Unit
| era_close Θ Γ Δ m m' :
  Θ ; Γ ; Δ ⊢ m ~ m' : Ch true Stop ->
  Θ ; Γ ; Δ ⊢ Close m ~ Close m' : IO Unit
(* conversion *)
| era_conv Θ Γ Δ A B m m' s :
  A ≃ B ->
  Θ ; Γ ; Δ ⊢ m ~ m' : A ->
  Γ ⊢ B : Sort s ->
  Θ ; Γ ; Δ ⊢ m ~ m' : B
where "Θ ; Γ ; Δ ⊢ m ~ n : A" := (era_type Θ Γ Δ m n A).
