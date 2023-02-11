From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx dyn_ctx sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive cvar_pos : dyn_ctx -> cvar -> bool -> Prop :=
| cvar_pos_nil i :
  cvar_pos nil i false
| cvar_pos_ty Θ A :
  cvar_pos (A :L Θ) 0 true
| cvar_pos_n Θ :
  cvar_pos (_: Θ) 0 false
| cvar_pos_cons Θ x A b :
  cvar_pos Θ x b ->
  cvar_pos (A :: Θ) x.+1 b.

Inductive sta0_type : dyn_ctx -> sta_ctx -> term -> term -> Prop :=
(* core *)
| sta0_axiom Θ Γ s :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ (Sort s) (Sort U)
| sta0_var Θ Γ x A :
  sta0_wf Θ Γ ->
  sta_has Γ x A ->
  sta0_type Θ Γ (Var x) A
| sta0_pi0 Θ Γ A B s r t :
  sta0_type Θ Γ A (Sort r) ->
  sta0_type Θ (A :: Γ) B (Sort t) ->
  sta0_type Θ Γ (Pi0 A B s) (Sort s)
| sta0_pi1 Θ Γ A B s r t :
  sta0_type Θ Γ A (Sort r) ->
  sta0_type Θ (A :: Γ) B (Sort t) ->
  sta0_type Θ Γ (Pi1 A B s) (Sort s)
| sta0_lam0 Θ Γ A B m s r :
  sta0_type Θ Γ A (Sort r) ->
  sta0_type Θ (A :: Γ) m B ->
  sta0_type Θ Γ (Lam0 A m s) (Pi0 A B s)
| sta0_lam1 Θ Γ A B m s r :
  sta0_type Θ Γ A (Sort r) ->
  sta0_type Θ (A :: Γ) m B ->
  sta0_type Θ Γ (Lam1 A m s) (Pi1 A B s)
| sta0_app0 Θ Γ A B m n s :
  sta0_type Θ Γ m (Pi0 A B s) ->
  sta0_type Θ Γ n A ->
  sta0_type Θ Γ (App m n) B.[n/]
| sta0_app1 Θ Γ A B m n s :
  sta0_type Θ Γ m (Pi1 A B s) ->
  sta0_type Θ Γ n A ->
  sta0_type Θ Γ (App m n) B.[n/]
| sta0_sig0 Θ Γ A B s r t :
  r ⊑ t ->
  sta0_type Θ Γ A (Sort s) ->
  sta0_type Θ (A :: Γ) B (Sort r) ->
  sta0_type Θ Γ (Sig0 A B t) (Sort t)
| sta0_sig1 Θ Γ A B s r t :
  s ⊑ t ->
  r ⊑ t ->
  sta0_type Θ Γ A (Sort s) ->
  sta0_type Θ (A :: Γ) B (Sort r) ->
  sta0_type Θ Γ (Sig1 A B t) (Sort t)
| sta0_pair0 Θ Γ A B m n t :
  sta0_type Θ Γ (Sig0 A B t) (Sort t) ->
  sta0_type Θ Γ m A ->
  sta0_type Θ Γ n B.[m/] ->
  sta0_type Θ Γ (Pair0 m n t) (Sig0 A B t)
| sta0_pair1 Θ Γ A B m n t :
  sta0_type Θ Γ (Sig1 A B t) (Sort t) ->
  sta0_type Θ Γ m A ->
  sta0_type Θ Γ n B.[m/] ->
  sta0_type Θ Γ (Pair1 m n t) (Sig1 A B t)
| sta0_letin0 Θ Γ A B C m n s t :
  sta0_type Θ (Sig0 A B t :: Γ) C (Sort s) ->
  sta0_type Θ Γ m (Sig0 A B t) ->
  sta0_type Θ (B :: A :: Γ) n C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  sta0_type Θ Γ (LetIn C m n) C.[m/]
| sta0_letin1 Θ Γ A B C m n s t :
  sta0_type Θ (Sig1 A B t :: Γ) C (Sort s) ->
  sta0_type Θ Γ m (Sig1 A B t) ->
  sta0_type Θ (B :: A :: Γ) n C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  sta0_type Θ Γ (LetIn C m n) C.[m/]
| sta0_fix Θ Γ A m s :
  sta0_type Θ Γ A (Sort s) ->
  sta0_type Θ (A :: Γ) m A.[ren (+1)] ->
  sta0_type Θ Γ (Fix A m) A
(* data *)
| sta0_unit Θ Γ :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ Unit (Sort U)
| sta0_ii Θ Γ :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ II Unit
| sta0_bool Θ Γ :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ Bool (Sort U)
| sta0_tt Θ Γ :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ TT Bool
| sta0_ff Θ Γ :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ FF Bool
| sta0_ifte Θ Γ A m n1 n2 s :
  sta0_type Θ (Bool :: Γ) A (Sort s) ->
  sta0_type Θ Γ m Bool ->
  sta0_type Θ Γ n1 A.[TT/] ->
  sta0_type Θ Γ n2 A.[FF/] ->
  sta0_type Θ Γ (Ifte A m n1 n2) A.[m/]
(* monadic *)
| sta0_io Θ Γ A s :
  sta0_type Θ Γ A (Sort s) ->
  sta0_type Θ Γ (IO A) (Sort L)
| sta0_return Θ Γ m A :
  sta0_type Θ Γ m A ->
  sta0_type Θ Γ (Return m) (IO A)
| sta0_bind Θ Γ m n A B s :
  sta0_type Θ Γ B (Sort s) ->
  sta0_type Θ Γ m (IO A) ->
  sta0_type Θ (A :: Γ) n (IO B.[ren (+1)]) ->
  sta0_type Θ Γ (Bind m n) (IO B)
(* session *)
| sta0_proto Θ Γ :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ Proto (Sort U)
| sta0_stop Θ Γ r :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ (Stop r) Proto
| sta0_act0 Θ Γ r A B s :
  sta0_type Θ Γ A (Sort s) ->
  sta0_type Θ (A :: Γ) B Proto ->
  sta0_type Θ Γ (Act0 r A B) Proto
| sta0_act1 Θ Γ r A B s :
  sta0_type Θ Γ A (Sort s) ->
  sta0_type Θ (A :: Γ) B Proto ->
  sta0_type Θ Γ (Act1 r A B) Proto
| sta0_ch Θ Γ r A :
  sta0_type Θ Γ A Proto ->
  sta0_type Θ Γ (Ch r A) (Sort L)
| sta0_cvar Θ Γ r x A :
  sta0_wf Θ Γ ->
  cvar_pos Θ x true ->
  sta0_type Θ nil A Proto ->
  sta0_type Θ Γ (CVar x) (Ch r A.[ren (+size Γ)])
| sta0_fork Θ Γ A m s :
  sta0_type Θ Γ (Ch true A) (Sort s) ->
  sta0_type Θ (Ch true A :: Γ) m (IO Unit) ->
  sta0_type Θ Γ (Fork A m) (IO (Ch false A))
| sta0_recv0 Θ Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  sta0_type Θ Γ m (Ch r1 (Act0 r2 A B)) ->
  sta0_type Θ Γ (Recv0 m) (IO (Sig0 A (Ch r1 B) L))
| sta0_recv1 Θ Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  sta0_type Θ Γ m (Ch r1 (Act1 r2 A B)) ->
  sta0_type Θ Γ (Recv1 m) (IO (Sig1 A (Ch r1 B) L))
| sta0_send0 Θ Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  sta0_type Θ Γ m (Ch r1 (Act0 r2 A B)) ->
  sta0_type Θ Γ (Send0 m) (Pi0 A (IO (Ch r1 B)) L)
| sta0_send1 Θ Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  sta0_type Θ Γ m (Ch r1 (Act1 r2 A B)) ->
  sta0_type Θ Γ (Send1 m) (Pi1 A (IO (Ch r1 B)) L)
| sta0_wait Θ Γ r1 r2 m :
  r1 (+) r2 = false ->
  sta0_type Θ Γ m (Ch r1 (Stop r2)) ->
  sta0_type Θ Γ (Wait m) (IO Unit)
| sta0_close Θ Γ r1 r2 m :
  r1 (+) r2 = true ->
  sta0_type Θ Γ m (Ch r1 (Stop r2)) ->
  sta0_type Θ Γ (Close m) (IO Unit)
(* conversion *)
| sta0_conv Θ Γ A B m s :
  A === B ->
  sta0_type Θ Γ m A ->
  sta0_type Θ Γ B (Sort s) ->
  sta0_type Θ Γ m B

with sta0_wf : dyn_ctx -> sta_ctx -> Prop :=
| sta0_wf_nil Θ : sta0_wf Θ nil
| sta0_wf_cons Θ Γ A s :
  sta0_wf Θ Γ ->
  sta0_type Θ Γ A (Sort s) ->
  sta0_wf Θ (A :: Γ).

Scheme sta0_type_mut := Induction for sta0_type Sort Prop
with sta0_wf_mut := Induction for sta0_wf Sort Prop.

Lemma sta0_type_wf Θ Γ m A : sta0_type Θ Γ m A -> sta0_wf Θ Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
Hint Resolve sta0_type_wf.

Reserved Notation "Θ ; Γ ⊢ m : A" (at level 50, Γ, m, A at next level).
Inductive sta_type : dyn_ctx -> sta_ctx -> term -> term -> Prop :=
(* core *)
| sta_axiom Θ Γ s :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ Sort s : Sort U
| sta_var Θ Γ x A :
  sta_wf Θ Γ ->
  sta_has Γ x A ->
  Θ ; Γ ⊢ Var x : A
| sta_pi0 Θ Γ A B s r t :
  Θ ; Γ ⊢ A : Sort r ->
  Θ ; (A :: Γ) ⊢ B : Sort t ->
  Θ ; Γ ⊢ Pi0 A B s : Sort s
| sta_pi1 Θ Γ A B s r t :
  Θ ; Γ ⊢ A : Sort r ->
  Θ ; (A :: Γ) ⊢ B : Sort t ->
  Θ ; Γ ⊢ Pi1 A B s : Sort s
| sta_lam0 Θ Γ A B m s :
  Θ ; (A :: Γ) ⊢ m : B ->
  Θ ; Γ ⊢ Lam0 A m s : Pi0 A B s
| sta_lam1 Θ Γ A B m s :
  Θ ; (A :: Γ) ⊢ m : B ->
  Θ ; Γ ⊢ Lam1 A m s : Pi1 A B s
| sta_app0 Θ Γ A B m n s :
  Θ ; Γ ⊢ m : Pi0 A B s ->
  Θ ; Γ ⊢ n : A ->
  Θ ; Γ ⊢ App m n : B.[n/]
| sta_app1 Θ Γ A B m n s :
  Θ ; Γ ⊢ m : Pi1 A B s ->
  Θ ; Γ ⊢ n : A ->
  Θ ; Γ ⊢ App m n : B.[n/]
| sta_sig0 Θ Γ A B s r t :
  r ⊑ t ->
  Θ ; Γ ⊢ A : Sort s ->
  Θ ; (A :: Γ) ⊢ B : Sort r ->
  Θ ; Γ ⊢ Sig0 A B t : Sort t
| sta_sig1 Θ Γ A B s r t :
  s ⊑ t ->
  r ⊑ t ->
  Θ ; Γ ⊢ A : Sort s ->
  Θ ; (A :: Γ) ⊢ B : Sort r ->
  Θ ; Γ ⊢ Sig1 A B t : Sort t
| sta_pair0 Θ Γ A B m n t :
  Θ ; Γ ⊢ Sig0 A B t : Sort t ->
  Θ ; Γ ⊢ m : A ->
  Θ ; Γ ⊢ n : B.[m/] ->
  Θ ; Γ ⊢ Pair0 m n t : Sig0 A B t
| sta_pair1 Θ Γ A B m n t :
  Θ ; Γ ⊢ Sig1 A B t : Sort t ->
  Θ ; Γ ⊢ m : A ->
  Θ ; Γ ⊢ n : B.[m/] ->
  Θ ; Γ ⊢ Pair1 m n t : Sig1 A B t
| sta_letin0 Θ Γ A B C m n s t :
  Θ ; (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Θ ; Γ ⊢ m : Sig0 A B t ->
  Θ ; (B :: A :: Γ) ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Θ ; Γ ⊢ LetIn C m n : C.[m/]
| sta_letin1 Θ Γ A B C m n s t :
  Θ ; (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Θ ; Γ ⊢ m : Sig1 A B t ->
  Θ ; (B :: A :: Γ) ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Θ ; Γ ⊢ LetIn C m n : C.[m/]
| sta_fix Θ Γ A m :
  Θ ; (A :: Γ) ⊢ m : A.[ren (+1)] ->
  Θ ; Γ ⊢ Fix A m : A
(* data *)
| sta_unit Θ Γ :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ Unit : Sort U
| sta_ii Θ Γ :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ II : Unit
| sta_bool Θ Γ :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ Bool : Sort U
| sta_tt Θ Γ :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ TT : Bool
| sta_ff Θ Γ :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ FF : Bool
| sta_ifte Θ Γ A m n1 n2 s :
  Θ ; (Bool :: Γ) ⊢ A : Sort s ->
  Θ ; Γ ⊢ m : Bool ->
  Θ ; Γ ⊢ n1 : A.[TT/] ->
  Θ ; Γ ⊢ n2 : A.[FF/] ->
  Θ ; Γ ⊢ Ifte A m n1 n2 : A.[m/]
(* monadic *)
| sta_io Θ Γ A s :
  Θ ; Γ ⊢ A : Sort s ->
  Θ ; Γ ⊢ IO A : Sort L
| sta_return Θ Γ m A :
  Θ ; Γ ⊢ m : A ->
  Θ ; Γ ⊢ Return m : IO A
| sta_bind Θ Γ m n A B s :
  Θ ; Γ ⊢ B : Sort s ->
  Θ ; Γ ⊢ m : IO A ->
  Θ ; (A :: Γ) ⊢ n : IO B.[ren (+1)] ->
  Θ ; Γ ⊢ Bind m n : IO B
(* session *)
| sta_proto Θ Γ :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ Proto : Sort U
| sta_stop Θ Γ r :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ Stop r : Proto
| sta_act0 Θ Γ r A B :
  Θ ; (A :: Γ) ⊢ B : Proto ->
  Θ ; Γ ⊢ Act0 r A B : Proto
| sta_act1 Θ Γ r A B :
  Θ ; (A :: Γ) ⊢ B : Proto ->
  Θ ; Γ ⊢ Act1 r A B : Proto
| sta_ch Θ Γ r A :
  Θ ; Γ ⊢ A : Proto ->
  Θ ; Γ ⊢ Ch r A : Sort L
| sta_cvar Θ Γ r x A :
  sta_wf Θ Γ ->
  cvar_pos Θ x true ->
  Θ ; nil ⊢ A : Proto ->
  Θ ; Γ ⊢ CVar x : Ch r A.[ren (+size Γ)]
| sta_fork Θ Γ m A :
  Θ ; (Ch true A :: Γ) ⊢ m : IO Unit ->
  Θ ; Γ ⊢ Fork A m : IO (Ch false A)
| sta_recv0 Θ Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  Θ ; Γ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Θ ; Γ ⊢ Recv0 m : IO (Sig0 A (Ch r1 B) L)
| sta_recv1 Θ Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  Θ ; Γ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Θ ; Γ ⊢ Recv1 m : IO (Sig1 A (Ch r1 B) L)
| sta_send0 Θ Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  Θ ; Γ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Θ ; Γ ⊢ Send0 m : Pi0 A (IO (Ch r1 B)) L
| sta_send1 Θ Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  Θ ; Γ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Θ ; Γ ⊢ Send1 m : Pi1 A (IO (Ch r1 B)) L
| sta_wait Θ Γ r1 r2 m :
  r1 (+) r2 = false ->
  Θ ; Γ ⊢ m : Ch r1 (Stop r2) ->
  Θ ; Γ ⊢ Wait m : IO Unit
| sta_close Θ Γ r1 r2 m :
  r1 (+) r2 = true ->
  Θ ; Γ ⊢ m : Ch r1 (Stop r2) ->
  Θ ; Γ ⊢ Close m : IO Unit
(* conversion *)
| sta_conv Θ Γ A B m s :
  A === B ->
  Θ ; Γ ⊢ m : A ->
  Θ ; Γ ⊢ B : Sort s ->
  Θ ; Γ ⊢ m : B
where "Θ ; Γ ⊢ m : A" := (sta_type Θ Γ m A)

with sta_wf : dyn_ctx -> sta_ctx -> Prop :=
| sta_wf_nil Θ : sta_wf Θ nil
| sta_wf_cons Θ Γ A s :
  sta_wf Θ Γ ->
  Θ ; Γ ⊢ A : Sort s ->
  sta_wf Θ (A :: Γ).

Scheme sta_type_mut := Induction for sta_type Sort Prop
with sta_wf_mut := Induction for sta_wf Sort Prop.

Lemma sta_type_wf Θ Γ m A : Θ ; Γ ⊢ m : A -> sta_wf Θ Γ.
Proof with eauto.
  elim=>{Θ Γ m A}...
  { move=>Θ Γ A _ _ _ _ wf. inv wf... }
  { move=>Θ Γ A _ _ _ _ wf. inv wf... }
  { move=>Θ Γ A _ _ wf. inv wf... }
  { move=>Θ Γ _ A _ _ wf. inv wf... }
  { move=>Θ Γ _ A _ _ wf. inv wf... }
  { move=>Θ Γ _ A _ wf. inv wf... }
Qed.
Hint Resolve sta_type_wf.

Lemma sta_sta0_type Θ Γ m A : Θ ; Γ ⊢ m : A -> sta0_type Θ Γ m A.
Proof with eauto using sta0_type, sta0_wf.
  move:Θ Γ m A. apply:(@sta_type_mut _ (fun Θ Γ wf => sta0_wf Θ Γ))...
  { move=>Θ Γ A B m s tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_lam0... }
  { move=>Θ Γ A B m s tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_lam1... }
  { move=>Θ Γ A m tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_fix... }
  { move=>Θ Γ r A B tyB ihB.
    have wf0:=sta0_type_wf ihB. inv wf0.
    apply: sta0_act0... }
  { move=>Θ Γ r A B tyB ihB.
    have wf0:=sta0_type_wf ihB. inv wf0.
    apply: sta0_act1... }
  { move=>Θ Γ m A tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_fork... }
  Unshelve. all: eauto using nat, bool.
Qed.
Hint Resolve sta_sta0_type.

Lemma sta0_sta_type Θ Γ m A : sta0_type Θ Γ m A -> Θ ; Γ ⊢ m : A.
Proof with eauto using sta_type, sta_wf.
  move:Θ Γ m A. apply:(@sta0_type_mut _ (fun Θ Γ wf => sta_wf Θ Γ))...
  Unshelve. all: eauto using nat, bool.
Qed.
