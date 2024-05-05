From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint arity_proto (A : term) : Prop :=
  match A with
  | Proto => True
  | Pi0 _ B s => arity_proto B
  | Pi1 _ B s => arity_proto B
  | _ => False
  end.

Fixpoint guarded (x : var) (m : term) : Prop :=
  match m with
  | Var y => x <> y 
  | Sort s => True
  | Pi0 A B s => guarded x A /\ guarded x.+1 B
  | Pi1 A B s => guarded x A /\ guarded x.+1 B
  | Lam0 A m s => guarded x A /\ guarded x.+1 m
  | Lam1 A m s => guarded x A /\ guarded x.+1 m
  | App0 m n => guarded x m /\ guarded x n
  | App1 m n => guarded x m /\ guarded x n
  | Sig0 A B s => guarded x A /\ guarded x.+1 B
  | Sig1 A B s => guarded x A /\ guarded x.+1 B
  | Pair0 m n s => guarded x m /\ guarded x n
  | Pair1 m n s => guarded x m /\ guarded x n
  | LetIn A m n => guarded x.+1 A /\ guarded x m /\ guarded x.+2 n
  | Fix A m => guarded x A /\ guarded x.+1 m
  | Unit => True | II => True
  | Bool => True | TT => True | FF => True
  | Ifte A m n1 n2 => guarded x.+1 A /\ guarded x m /\ guarded x n1 /\ guarded x n2
  | IO A => guarded x A
  | Return m => guarded x m
  | Bind m n => guarded x m /\ guarded x.+1 n
  | Proto => True | Stop => True
  | Act0 r A B => guarded x A
  | Act1 r A B => guarded x A
  | Ch r A => guarded x A
  | CVar x => True
  | Fork A m => guarded x A /\ guarded x.+1 m
  | Recv0 m => guarded x m | Recv1 m => guarded x m
  | Send0 m => guarded x m | Send1 m => guarded x m
  | Close m => guarded x m | Wait m => guarded x m
  | Box => True
  end.

Inductive sta0_type : sta_ctx -> term -> term -> Prop :=
(* core *)
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
  sta0_type Γ (App0 m n) B.[n/]
| sta0_app1 Γ A B m n s :
  sta0_type Γ m (Pi1 A B s) ->
  sta0_type Γ n A ->
  sta0_type Γ (App1 m n) B.[n/]
| sta0_sig0 Γ A B s r t :
  r ⊑ t ->
  sta0_type Γ A (Sort s) ->
  sta0_type (A :: Γ) B (Sort r) ->
  sta0_type Γ (Sig0 A B t) (Sort t)
| sta0_sig1 Γ A B s r t :
  s ⊑ t ->
  r ⊑ t ->
  sta0_type Γ A (Sort s) ->
  sta0_type (A :: Γ) B (Sort r) ->
  sta0_type Γ (Sig1 A B t) (Sort t)
| sta0_pair0 Γ A B m n t :
  sta0_type Γ (Sig0 A B t) (Sort t) ->
  sta0_type Γ m A ->
  sta0_type Γ n B.[m/] ->
  sta0_type Γ (Pair0 m n t) (Sig0 A B t)
| sta0_pair1 Γ A B m n t :
  sta0_type Γ (Sig1 A B t) (Sort t) ->
  sta0_type Γ m A ->
  sta0_type Γ n B.[m/] ->
  sta0_type Γ (Pair1 m n t) (Sig1 A B t)
| sta0_letin0 Γ A B C m n s t :
  sta0_type (Sig0 A B t :: Γ) C (Sort s) ->
  sta0_type Γ m (Sig0 A B t) ->
  sta0_type (B :: A :: Γ) n C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  sta0_type Γ (LetIn C m n) C.[m/]
| sta0_letin1 Γ A B C m n s t :
  sta0_type (Sig1 A B t :: Γ) C (Sort s) ->
  sta0_type Γ m (Sig1 A B t) ->
  sta0_type (B :: A :: Γ) n C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  sta0_type Γ (LetIn C m n) C.[m/]
| sta0_fix Γ A m s :
  arity_proto A ->
  guarded 0 m ->
  sta0_type Γ A (Sort s) ->
  sta0_type (A :: Γ) m A.[ren (+1)] ->
  sta0_type Γ (Fix A m) A
(* data *)
| sta0_unit Γ :
  sta0_wf Γ ->
  sta0_type Γ Unit (Sort U)
| sta0_ii Γ :
  sta0_wf Γ ->
  sta0_type Γ II Unit
| sta0_bool Γ :
  sta0_wf Γ ->
  sta0_type Γ Bool (Sort U)
| sta0_tt Γ :
  sta0_wf Γ ->
  sta0_type Γ TT Bool
| sta0_ff Γ :
  sta0_wf Γ ->
  sta0_type Γ FF Bool
| sta0_ifte Γ A m n1 n2 s :
  sta0_type (Bool :: Γ) A (Sort s) ->
  sta0_type Γ m Bool ->
  sta0_type Γ n1 A.[TT/] ->
  sta0_type Γ n2 A.[FF/] ->
  sta0_type Γ (Ifte A m n1 n2) A.[m/]
(* monadic *)
| sta0_io Γ A s :
  sta0_type Γ A (Sort s) ->
  sta0_type Γ (IO A) (Sort L)
| sta0_return Γ m A :
  sta0_type Γ m A ->
  sta0_type Γ (Return m) (IO A)
| sta0_bind Γ m n A B s :
  sta0_type Γ B (Sort s) ->
  sta0_type Γ m (IO A) ->
  sta0_type (A :: Γ) n (IO B.[ren (+1)]) ->
  sta0_type Γ (Bind m n) (IO B)
(* session *)
| sta0_proto Γ :
  sta0_wf Γ ->
  sta0_type Γ Proto (Sort U)
| sta0_stop Γ :
  sta0_wf Γ ->
  sta0_type Γ Stop Proto
| sta0_act0 Γ r A B s :
  sta0_type Γ A (Sort s) ->
  sta0_type (A :: Γ) B Proto ->
  sta0_type Γ (Act0 r A B) Proto
| sta0_act1 Γ r A B s :
  sta0_type Γ A (Sort s) ->
  sta0_type (A :: Γ) B Proto ->
  sta0_type Γ (Act1 r A B) Proto
| sta0_ch Γ r A :
  sta0_type Γ A Proto ->
  sta0_type Γ (Ch r A) (Sort L)
| sta0_cvar Γ r x A :
  sta0_wf Γ ->
  sta0_type nil A Proto ->
  sta0_type Γ (CVar x) (Ch r A.[ren (+size Γ)])
| sta0_fork Γ A m s :
  sta0_type Γ (Ch true A) (Sort s) ->
  sta0_type (Ch true A :: Γ) m (IO Unit) ->
  sta0_type Γ (Fork A m) (IO (Ch false A))
| sta0_recv0 Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  sta0_type Γ m (Ch r1 (Act0 r2 A B)) ->
  sta0_type Γ (Recv0 m) (IO (Sig0 A (Ch r1 B) L))
| sta0_recv1 Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  sta0_type Γ m (Ch r1 (Act1 r2 A B)) ->
  sta0_type Γ (Recv1 m) (IO (Sig1 A (Ch r1 B) L))
| sta0_send0 Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  sta0_type Γ m (Ch r1 (Act0 r2 A B)) ->
  sta0_type Γ (Send0 m) (Pi0 A (IO (Ch r1 B)) L)
| sta0_send1 Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  sta0_type Γ m (Ch r1 (Act1 r2 A B)) ->
  sta0_type Γ (Send1 m) (Pi1 A (IO (Ch r1 B)) L)
| sta0_wait Γ m :
  sta0_type Γ m (Ch false Stop) ->
  sta0_type Γ (Wait m) (IO Unit)
| sta0_close Γ m :
  sta0_type Γ m (Ch true Stop) ->
  sta0_type Γ (Close m) (IO Unit)
(* conversion *)
| sta0_conv Γ A B m s :
  A ≃ B ->
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
#[global] Hint Resolve sta0_type_wf.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive sta_type : sta_ctx -> term -> term -> Prop :=
(* core *)
| sta_axiom Γ s :
  sta_wf Γ ->
  Γ ⊢ Sort s : Sort U
| sta_var Γ x A :
  sta_wf Γ ->
  sta_has Γ x A ->
  Γ ⊢ Var x : A
| sta_pi0 Γ A B s r t :
  Γ ⊢ A : Sort r ->
  (A :: Γ) ⊢ B : Sort t ->
  Γ ⊢ Pi0 A B s : Sort s
| sta_pi1 Γ A B s r t :
  Γ ⊢ A : Sort r ->
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
  Γ ⊢ App0 m n : B.[n/]
| sta_app1 Γ A B m n s :
  Γ ⊢ m : Pi1 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App1 m n : B.[n/]
| sta_sig0 Γ A B s r t :
  r ⊑ t ->
  Γ ⊢ A : Sort s ->
  (A :: Γ) ⊢ B : Sort r ->
  Γ ⊢ Sig0 A B t : Sort t
| sta_sig1 Γ A B s r t :
  s ⊑ t ->
  r ⊑ t ->
  Γ ⊢ A : Sort s ->
  (A :: Γ) ⊢ B : Sort r ->
  Γ ⊢ Sig1 A B t : Sort t
| sta_pair0 Γ A B m n t :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair0 m n t : Sig0 A B t
| sta_pair1 Γ A B m n t :
  Γ ⊢ Sig1 A B t : Sort t ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair1 m n t : Sig1 A B t
| sta_letin0 Γ A B C m n s t :
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Γ ⊢ m : Sig0 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| sta_letin1 Γ A B C m n s t :
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Γ ⊢ m : Sig1 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| sta_fix Γ A m :
  arity_proto A ->
  guarded 0 m ->
  (A :: Γ) ⊢ m : A.[ren (+1)] ->
  Γ ⊢ Fix A m : A
(* data *)
| sta_unit Γ :
  sta_wf Γ ->
  Γ ⊢ Unit : Sort U
| sta_ii Γ :
  sta_wf Γ ->
  Γ ⊢ II : Unit
| sta_bool Γ :
  sta_wf Γ ->
  Γ ⊢ Bool : Sort U
| sta_tt Γ :
  sta_wf Γ ->
  Γ ⊢ TT : Bool
| sta_ff Γ :
  sta_wf Γ ->
  Γ ⊢ FF : Bool
| sta_ifte Γ A m n1 n2 s :
  (Bool :: Γ) ⊢ A : Sort s ->
  Γ ⊢ m : Bool ->
  Γ ⊢ n1 : A.[TT/] ->
  Γ ⊢ n2 : A.[FF/] ->
  Γ ⊢ Ifte A m n1 n2 : A.[m/]
(* monadic *)
| sta_io Γ A s :
  Γ ⊢ A : Sort s ->
  Γ ⊢ IO A : Sort L
| sta_return Γ m A :
  Γ ⊢ m : A ->
  Γ ⊢ Return m : IO A
| sta_bind Γ m n A B s :
  Γ ⊢ B : Sort s ->
  Γ ⊢ m : IO A ->
  (A :: Γ) ⊢ n : IO B.[ren (+1)] ->
  Γ ⊢ Bind m n : IO B
(* session *)
| sta_proto Γ :
  sta_wf Γ ->
  Γ ⊢ Proto : Sort U
| sta_stop Γ :
  sta_wf Γ ->
  Γ ⊢ Stop : Proto
| sta_act0 Γ r A B :
  (A :: Γ) ⊢ B : Proto ->
  Γ ⊢ Act0 r A B : Proto
| sta_act1 Γ r A B :
  (A :: Γ) ⊢ B : Proto ->
  Γ ⊢ Act1 r A B : Proto
| sta_ch Γ r A :
  Γ ⊢ A : Proto ->
  Γ ⊢ Ch r A : Sort L
| sta_cvar Γ r x A :
  sta_wf Γ ->
  nil ⊢ A : Proto ->
  Γ ⊢ CVar x : Ch r A.[ren (+size Γ)]
| sta_fork Γ m A :
  (Ch true A :: Γ) ⊢ m : IO Unit ->
  Γ ⊢ Fork A m : IO (Ch false A)
| sta_recv0 Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  Γ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Γ ⊢ Recv0 m : IO (Sig0 A (Ch r1 B) L)
| sta_recv1 Γ r1 r2 A B m :
  r1 (+) r2 = false ->
  Γ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Γ ⊢ Recv1 m : IO (Sig1 A (Ch r1 B) L)
| sta_send0 Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  Γ ⊢ m : Ch r1 (Act0 r2 A B) ->
  Γ ⊢ Send0 m : Pi0 A (IO (Ch r1 B)) L
| sta_send1 Γ r1 r2 A B m :
  r1 (+) r2 = true ->
  Γ ⊢ m : Ch r1 (Act1 r2 A B) ->
  Γ ⊢ Send1 m : Pi1 A (IO (Ch r1 B)) L
| sta_wait Γ m :
  Γ ⊢ m : Ch false Stop ->
  Γ ⊢ Wait m : IO Unit
| sta_close Γ m :
  Γ ⊢ m : Ch true Stop ->
  Γ ⊢ Close m : IO Unit
(* conversion *)
| sta_conv Γ A B m s :
  A ≃ B ->
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
  { move=>Γ _ A _ _ wf. inv wf... }
  { move=>Γ _ A _ _ wf. inv wf... }
  { move=>Γ _ A _ wf. inv wf... }
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
  { move=>Γ A m ar gr tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_fix... }
  { move=>Γ r A B tyB ihB.
    have wf0:=sta0_type_wf ihB. inv wf0.
    apply: sta0_act0... }
  { move=>Γ r A B tyB ihB.
    have wf0:=sta0_type_wf ihB. inv wf0.
    apply: sta0_act1... }
  { move=>Γ m A tym ihm.
    have wf0:=sta0_type_wf ihm. inv wf0.
    apply: sta0_fork... }
  Unshelve. all: eauto using nat, bool.
Qed.
#[global] Hint Resolve sta_sta0_type.

Lemma sta0_sta_type Γ m A : sta0_type Γ m A -> Γ ⊢ m : A.
Proof with eauto using sta_type, sta_wf.
  move:Γ m A. apply:(@sta0_type_mut _ (fun Γ wf => sta_wf Γ))...
  Unshelve. all: eauto using nat, bool.
Qed.

Lemma sta0_sta_wf Γ : sta0_wf Γ -> sta_wf Γ.
Proof with eauto using sta_wf.
  elim=>{Γ}...
  move=>Γ A s wf0 wf ty.
  econstructor...
  apply: sta0_sta_type...
Qed.
