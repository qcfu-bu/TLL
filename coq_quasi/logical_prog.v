From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_closed logical_sr logical_sn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv_logical_val :=
  match goal with
  | [ H : logical_val _ |- _ ] => inv H
  end.

Lemma logical_pi0_canonical Γ m A B C s :
  Γ ⊢ m : C -> C === Pi0 A B s -> closed 0 m -> logical_val m ->
  exists A n, m = Lam0 A n s.
Proof with eauto.
  move=>ty. elim: ty A B s=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf hs A0 B s eq h vl. inv h. inv H1. }
  { move=>Γ A B m s tym ihm A0 B0 s0/pi0_inj[eqA[eqB->]] _ _.
    exists A. exists m... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 eq2 h vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pi1_canonical Γ m A B C s :
  Γ ⊢ m : C -> C === Pi1 A B s -> closed 0 m -> logical_val m ->
  exists A n, m = Lam1 A n s.
Proof with eauto.
  move=>ty. elim: ty A B s=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf hs A0 B s eq h vl. inv h. inv H1. }
  { move=>Γ A B m s tym ihm A0 B0 s0/pi1_inj[eqA[eqB->]] _ _.
    exists A. exists m... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 eq2 h vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_sig0_canonical Γ m A B C s :
  Γ ⊢ m : C -> C === Sig0 A B s -> closed 0 m -> logical_val m ->
  exists m1 m2, m = Pair0 m1 m2 s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs A0 B0 s eq h. inv h. inv H1. }
  { move=>Γ A B m n t tyS _ tym _ tyn _ A0 B0 s0/sig0_inj[eqA[eqB->]] _ _.
    exists m. exists n... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 eq2 h vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_sig1_canonical Γ m A B C s :
  Γ ⊢ m : C -> C === Sig1 A B s -> closed 0 m -> logical_val m ->
  exists m1 m2, m = Pair1 m1 m2 s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs A0 B0 s eq h. inv h. inv H1. }
  { move=>Γ A B m n t tyS _ tym _ tyn _ A0 B0 s0/sig1_inj[eqA[eqB->]] _ _.
    exists m. exists n... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 eq2 h vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_with_canonical Γ m A B C s :
  Γ ⊢ m : C -> C === With A B s -> closed 0 m -> logical_val m ->
  exists m1 m2, m = APair m1 m2 s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs A0 B0 s eq h. inv h. inv H1. }
  { move=>Γ A B m n t tym _ tyn _ A0 B0 s0/with_inj[eqA[eqB->]] _ _.
    exists m. exists n... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 eq2 h vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_id_canonical Γ m C A x y :
  Γ ⊢ m : C -> C === Id A x y -> closed 0 m -> logical_val m ->
  exists n, m = Refl n.
Proof with eauto.
  move=>ty. elim: ty A x y=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs A0 x0 y eq h. inv h. inv H1. }
  { move=>Γ A m tym ihm A0 x y eq _ _.
    exists m... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 x y eq2 h vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_prog Γ m A : Γ ⊢ m : A -> closed 0 m -> (exists n, m ~> n) \/ logical_val m.
Proof with eauto using logical_step, logical_val.
  move=>ty. elim: ty=>{Γ m A}.
  { move=>Γ s wf h. right... }
  { move=>Γ x A wf shs h. inv h. inv H1. }
  { move=>Γ A B s r t tyA ihA tyB ihB h. right... }
  { move=>Γ A B s r t tyA ihA tyB ihB h. right... }
  { move=>Γ A B m s tym ihm h. right... }
  { move=>Γ A B m s tym ihm h. right... }
  { move=>Γ A B m n s tym ihm tyn ihn h. inv h.
    have[[m0 stm]|vlm]:=ihm H2.
    { left. exists (App m0 n)... }
    { have[[n0 stn]|vln]:=ihn H3.
      { left. exists (App m n0)... }
      { have[A0[n0 e]]:=logical_pi0_canonical tym (convR _ _) H2 vlm. subst.
        left. exists (n0.[n/])... } } }
  { move=>Γ A B m n s tym ihm tyn ihn h. inv h.
    have[[m0 stm]|vlm]:=ihm H2.
    { left. exists (App m0 n)... }
    { have[[n0 stn]|vln]:=ihn H3.
      { left. exists (App m n0)... }
      { have[A0[n0 e]]:=logical_pi1_canonical tym (convR _ _) H2 vlm. subst.
        left. exists (n0.[n/])... } } }
  { move=>Γ A B s r t leq tyA ihA tyB ihB h. right... }
  { move=>Γ A B s r t leq1 leq2 tyA ihA tyB ihB h. right... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn h. inv h.
    have[[m' stm]|vlm]:=ihm H2.
    { left. exists (Pair0 m' n t)... }
    { right... } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn h. inv h.
    have[[m' stm]|vlm]:=ihm H2.
    { left. exists (Pair1 m' n t)... }
    { have[[n' stn]|vln]:=ihn H4.
      { left. exists (Pair1 m n' t)... }
      { right... } } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn h. inv h.
    have[[m' stm]|vlm]:=ihm H4.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=logical_sig0_canonical tym (convR _ _) H4 vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn h. inv h.
    have[[m' stm]|vlm]:=ihm H4.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=logical_sig1_canonical tym (convR _ _) H4 vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ A B s r t tyA ihA tyB ihB h. right... }
  { move=>Γ A B m n t tym ihm tyn ihn h. right... }
  { move=>Γ A B m t tym ihm h. inv h.
    have[[m' stm]|vlm]:=ihm H1.
    { left. exists (Fst m')... }
    { have[m1[m2 e]]:=logical_with_canonical tym (convR _ _) H1 vlm. subst.
      left. exists m1... } }
  { move=>Γ A B m t tym ihm h. inv h.
    have[[m' stm]|vlm]:=ihm H1.
    { left. exists (Snd m')... }
    { have[m1[m2 e]]:=logical_with_canonical tym (convR _ _) H1 vlm. subst.
      left. exists m2... } }
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn h. right... }
  { move=>Γ A m tym ihm h. right... }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP h. inv h.
    have[[P0 stP]|vlP]:=ihP H7.
    { left. exists (Rw B H P0)... }
    { have[n0 e]:=logical_id_canonical tyP (convR _ _) H7 vlP. subst.
      left. exists H... } }
  { move=>Γ A B m s eq tym ihm tyB ihB e.
    apply: ihm... }
Qed.

Lemma logical_step_closed i m n : m ~> n -> closed i m -> closed i n.
Proof with eauto using closed.
  move=>st. elim: st i =>//{m n}.
  all: try solve
         [intros;
          match goal with
          | [ H : closed _ _ |- _ ] => inv H; eauto using closed
          end].
  { move=>A m n s i h. inv h. inv H2. apply: closed_subst1... }
  { move=>A m n s i h. inv h. inv H2. apply: closed_subst1... }
  { move=>A m1 m2 n s i h. inv h. inv H4. apply: closed_subst2... }
  { move=>A m1 m2 n s i h. inv h. inv H4. apply: closed_subst2... }
  { move=>m n s i h. inv h. inv H1... }
  { move=>m n s i h. inv h. inv H1... }
Qed.

Lemma logical_red_closed i m n : m ~>* n -> closed i m -> closed i n.
Proof with eauto using closed.
  move=>rd. elim: rd=>{n}...
  move=>y z rd ih st h.
  have:=ih h.
  by apply: logical_step_closed.
Qed.

Lemma logical_vnX Γ m A :
   sn logical_step m -> Γ ⊢ m : A -> closed 0 m -> (exists n, m ~>* n /\ logical_val n).
Proof with eauto.
  move=>pf. elim: pf A=>{m}.
  move=>m h ih A tym c.
  have[[m0 stm]|vlm]:=logical_prog tym c.
  { have tym0:=logical_sr tym stm.
    have[n[rn vln]]:=ih _ stm _ tym0 (logical_step_closed stm c).
    exists n. split...
    apply: starES... }
  { exists m... }
Qed.

Lemma logical_vn Γ m A :
  Γ ⊢ m : A -> closed 0 m -> (exists n, m ~>* n /\ logical_val n).
Proof with eauto.
  move=>tym.
  apply: logical_vnX...
  apply: logical_sn...
Qed.
