(** * Logical progress (primary theorem)

    [logical_prg]: a closed well-typed logical term either steps or is
    a value.

    Proof sketch — first prove a canonical-forms lemma per elimination
    target ([logical_pi0_canonical], [logical_pi1_canonical],
    [logical_sig0_canonical], [logical_sig1_canonical],
    [logical_bool_canonical], [logical_id_canonical]): a closed value
    whose type is convertible to [Pi0 A B s] must be a [Lam0 _ _ s],
    and so on. Each is by induction on the typing, peeling off
    [logical_conv] with transitivity of [≃]. Then [logical_prg] is
    induction on [Γ ⊢ m : A] with the nil-context assumption: variable
    case is impossible; intro forms are values; each elim form recurses
    on the principal argument and, when it is a value, uses the
    matching canonical-forms lemma to fire the corresponding β/ι/if
    reduction. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv_logical_val :=
  match goal with
  | [ H : logical_val _ |- _ ] => inv H
  end.

Lemma logical_pi0_canonical m A B C s :
  nil ⊢ m : C -> C ≃ Pi0 A B s -> logical_val m ->
  exists A n, m = Lam0 A n s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e A0 B s eq vl. subst. inv shs. }
  { move=>Γ A B m s tym ihm e1 A0 B0 s0/pi0_inj[eqA[eqB e2]] vl. subst.
    exists A. exists m... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pi1_canonical m A B C s :
  nil ⊢ m : C -> C ≃ Pi1 A B s -> logical_val m ->
  exists A n, m = Lam1 A n s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m s tym ihm e1 A0 B0 s0/pi1_inj[eqA[eqB e2]] vl. subst.
    exists A. exists m... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_sig0_canonical m A B C s :
  nil ⊢ m : C -> C ≃ Sig0 A B s -> logical_val m ->
  exists m1 m2, m = Pair0 m1 m2 s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m n t l tyS _ tym _ tyn _ e1 A0 B0 s0/sig0_inj[eqA[eqB e2]] vl.
    subst. exists m. exists n... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_sig1_canonical m A B C s :
  nil ⊢ m : C -> C ≃ Sig1 A B s -> logical_val m ->
  exists m1 m2, m = Pair1 m1 m2 s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m n t l tyS _ tym _ tyn _ e1 A0 B0 s0/sig1_inj[eqA[eqB e2]] vl.
    subst. exists m. exists n... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_bool_canonical m C :
  nil ⊢ m : C -> C ≃ Bool -> logical_val m -> m = TT \/ m = FF.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ wf e _ vl. left... }
  { move=>Γ wf e _ vl. right... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB e eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_id_canonical m C A x y :
  nil ⊢ m : C -> C ≃ Id A x y -> logical_val m ->
  exists n, m = Refl n.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A x y=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A m tym ihm e A0 x y eq vl.
    exists m... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB e A0 x y eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_prg m A : nil ⊢ m : A -> (exists n, m ~> n) \/ logical_val m.
Proof with eauto using logical_step, logical_val.
  move e:(nil)=>Γ ty. elim: ty e=>{Γ m A}.
  { move=>Γ s wf e. right... }
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B s r t l1 l2 tyA ihA tyB ihB e. right... }
  { move=>Γ A B s r t l1 l2 tyA ihA tyB ihB e. right... }
  { move=>Γ A B m s tym ihm e. right... }
  { move=>Γ A B m s tym ihm e. right... }
  { move=>Γ A B m n s tym ihm tyn ihn e. subst.
    have[[m0 stm]|vlm]:=ihm erefl.
    { left. exists (App m0 n)... }
    { have[[n0 stn]|vln]:=ihn erefl.
      { left. exists (App m n0)... }
      { have[A0[n0 e]]:=logical_pi0_canonical tym (convR _ _) vlm. subst.
        left. exists (n0.[n/])... } } }
  { move=>Γ A B m n s tym ihm tyn ihn e. subst.
    have[[m0 stm]|vlm]:=ihm erefl.
    { left. exists (App m0 n)... }
    { have[[n0 stn]|vln]:=ihn erefl.
      { left. exists (App m n0)... }
      { have[A0[n0 e]]:=logical_pi1_canonical tym (convR _ _) vlm. subst.
        left. exists (n0.[n/])... } } }
  { move=>Γ A B s r t l1 l2 leq tyA ihA tyB ihB e. right... }
  { move=>Γ A B s r t l1 l2 leq1 leq2 tyA ihA tyB ihB e. right... }
  { move=>Γ A B m n t l tyS ihS tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (Pair0 m' n t)... }
    { right... } }
  { move=>Γ A B m n t l tyS ihS tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (Pair1 m' n t)... }
    { have[[n' stn]|vln]:=ihn erefl.
      { left. exists (Pair1 m n' t)... }
      { right... } } }
  { move=>Γ A B C m n s t l tyC ihC tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=logical_sig0_canonical tym (convR _ _) vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ A B C m n s t l tyC ihC tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=logical_sig1_canonical tym (convR _ _) vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ wf e. right... }
  { move=>Γ wf e. right... }
  { move=>Γ wf e. right... }
  { move=>Γ A m n1 n2 s l tyA _ tym ihm tyn1 ihn1 tyn2 ihn2 e. subst.
    have[[m' st]|vlm]:=ihm erefl.
    { left. exists (Ifte A m' n1 n2)... }
    { have[e|e]:=logical_bool_canonical tym (convR _ _) vlm; subst.
      left. exists n1... left. exists n2... } }
  { move=>Γ A m n s l tyA ihA tym ihm tyn ihn e. right... }
  { move=>Γ A m tym ihm e. right... }
  { move=>Γ A B H P m n s l tyB ihB tyH ihH tyP ihP e. subst.
    have[[P0 stP]|vlP]:=ihP erefl.
    { left. exists (Rw B H P0)... }
    { have[n0 e]:=logical_id_canonical tyP (convR _ _) vlP. subst.
      left. exists H... } }
  { move=>Γ A B m s l eq tym ihm tyB ihB e.
    apply: ihm... }
Qed.