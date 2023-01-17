From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_uniq sta_sr dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_lam0_invX Γ Δ A1 A2 B C m s1 s2 t :
  Γ ; Δ ⊢ Lam0 A1 m s1 : C ->
  C === Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  (A2 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s k tym _ A1 A2 B0 m0
      s1 s2 t[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: dyn_ctx_conv0.
    apply: conv_sym...
    exact: H4.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam1_invX Γ Δ A1 A2 B C m s1 s2 t :
  Γ ; Δ ⊢ Lam1 A1 m s1 : C ->
  C === Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  exists r, (A2 :: Γ) ; A2 :{r} Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s t k tym _ A1 A2 B0 m0
      s1 s2 t0[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_rd H4 rd1.
    have tyA0s:=sta_rd H3 rd2.
    have/sort_inj e:=sta_uniq tyA0t tyA0s. subst.
    exists s.
    apply: dyn_ctx_conv1.
    apply: conv_sym...
    exact: H3.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam0_inv Γ Δ m A1 A2 B s1 s2 :
  Γ ; Δ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> (A1 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi0_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam0_invX...
Qed.

Lemma dyn_lam1_inv Γ Δ m A1 A2 B s1 s2 :
  Γ ; Δ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> exists r, (A1 :: Γ) ; A1 :{r} Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi1_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam1_invX...
Qed.

Lemma dyn_return_inv Γ Δ m B :
  Γ ; Δ ⊢ Return m : B ->
  exists A, Γ ; Δ ⊢ m : A /\ B === IO A.
Proof with eauto.
  move e:(Return m)=>x ty.
  elim: ty m e=>//{Γ Δ B x}.
  { move=>Γ Δ m A tym ihm m0[e]; subst. exists A... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB m0 e; subst.
    have[A0[tym0 eq2]]:=ihm _ erefl.
    exists A0. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma dyn_app_inv Γ Δ m n C :
  Γ ; Δ ⊢ App m n : C ->
  exists A B s,
    (Γ ; Δ ⊢ m : Pi0 A B s /\ Γ ⊢ n : A /\ C === B.[n/]) \/
    (exists Δ1 Δ2, Γ ; Δ1 ⊢ m : Pi1 A B s /\ Δ1 ∘ Δ2 => Δ /\ Γ ; Δ2 ⊢ n : A /\ C === B.[n/]).
Proof with eauto.
  move e:(App m n)=>x ty.
  elim: ty m n e=>//{Γ Δ x C}.
  { move=>Γ Δ A B m n s tym ihm tyn m0 n0[e1 e2]; subst.
    exists A. exists B. exists s. left. split... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn m0 n0[e1 e2]; subst.
    exists A. exists B. exists s. right. exists Δ1. exists Δ2. split... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB m0 n0 e; subst.
    have[A0[B0[s0[[tym0[tyn0 eq2]]|[Δ1[Δ2[tym0[mrg[tyn0 eq2]]]]]]]]]:=ihm _ _ erefl.
    { exists A0. exists B0. exists s0. left. repeat split...
      apply: conv_trans.
      apply: conv_sym...
      exact: eq2. }
    { exists A0. exists B0. exists s0. right. exists Δ1. exists Δ2. repeat split...
      apply: conv_trans.
      apply: conv_sym...
      exact: eq2. } }
Qed.

Lemma dyn_it_inv Γ Δ A :
  Γ ; Δ ⊢ It : A -> A === Unit /\ Δ ▷ U.
Proof with eauto.
  move e:(It)=>x ty.
  elim: ty e=>//{Γ Δ x A}.
  move=>Γ Δ A B m s eq1 tym ihm tyB e; subst.
  have[eq2 k]:=ihm erefl. split...
  apply: conv_trans.
  apply: conv_sym...
  exact: eq2.
Qed.

Lemma dyn_rand_inv Γ Δ A :
  Γ ; Δ ⊢ Rand : A -> A === Pi1 Unit (IO Nat) U /\ Δ ▷ U.
Proof with eauto.
  move e:(Rand)=>x ty.
  elim: ty e=>//{Γ Δ x A}.
  move=>Γ Δ A B m s eq1 tym ihm tyB e; subst.
  have[eq2 k]:=ihm erefl. split...
  apply: conv_trans.
  apply: conv_sym...
  exact: eq2.
Qed.
