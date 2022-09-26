From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_sr sta_uniq dyn_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_sta_step m n : m ~>> n -> m ~> n.
Proof with eauto using sta_step. elim... Qed.

Lemma dyn_val_key Γ Δ m A s :
  dyn_wf Γ Δ -> Γ ; Δ ⊢ m : A -> Γ ⊢ A : @s -> dyn_val m -> Δ ▷ s.
Proof with eauto using key_impure.
  destruct s...
  move=>wf ty. elim: ty wf=>{Γ Δ m A}.
  { move=>Γ Δ x A shs dhs wf tyA vl. inv vl. }
  { move=>Γ Δ A B m s t k tyP1 mrg ih wf tyP2 vl.
    have[_[_[_/sort_inj->//]]]:=sta_pi0_inv tyP2. }
  { move=>Γ Δ A B m s t k tyP1 mrg ih wf tyP2 vl.
    have[_[_[_/sort_inj->//]]]:=sta_pi1_inv tyP2. }
  { move=>Γ Δ A B m n s t tym ih tyn wf tyB vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn wf tyB vl. inv vl. }
  { move=>Γ Δ A B m [] eq tym ihm tyB1 wf tyB2 vl.
    { have[[] tyA]:=dyn_valid wf tym...
      have[x r1 r2]:=church_rosser eq.
      have tyx1:=sta_rd (dyn_sta_wf wf) tyA r1.
      have tyx2:=sta_rd (dyn_sta_wf wf) tyB2 r2.
      exfalso.
      have{}eq:=sta_uniq tyx1 tyx2.
      solve_conv. }
    { exfalso.
      have{}eq:=sta_uniq tyB1 tyB2.
      solve_conv. } }
Qed.

Theorem dyn_sr Γ Δ m n A :
  dyn_wf Γ Δ -> Γ ; Δ ⊢ m : A -> m ~>> n -> Γ ; Δ ⊢ n : A.
Proof with eauto using dyn_type, dyn_step, dyn_wf.
  move=>wf ty. elim: ty n wf=>{Γ Δ m A}...
  { move=>Γ Δ x A0 shs dhs n wf st. inv st. }
  { move=>Γ Δ A B m s t k tyP tym ihm n wf st. inv st. }
  { move=>Γ Δ A B m s t k tyP tym ihm n wf st. inv st. }
  { move=>Γ Δ A B m n s t tym ihm tyn ihn wf st. inv st.
    { have tym':=ihm _ wf H2.
      apply: dyn_app0... }
    { have tyn':=sta_sr (dyn_sta_wf wf) tyn (dyn_sta_step H2).
      have[x tyP]:=dyn_valid wf tym.
      have[r[_[tyB _]]]:=sta_pi0_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv1i.
      apply: dyn_sta_step...
      apply: dyn_app0...
      have:=sta_subst tyB tyn.
      asimpl... }
    { have[x tyP]:=dyn_valid wf tym.
      have[tym0 _]:=dyn_lam0_inv wf tyP tym.
      apply: dyn_subst0... }
    { exfalso.
      apply: sta_lam1_pi0_false...
      apply: dyn_sta_type... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn n0 wf st. inv st.
    { have[wf1 wf2]:=dyn_wf_merge mrg wf.
      have tym':=ihm _ wf1 H2.
      apply: dyn_app1... }
    { have[wf1 wf2]:=dyn_wf_merge mrg wf.
      have tyn':=ihn _ wf2 H2.
      have[x tyP]:=dyn_valid wf1 tym.
      have[r[_[tyB _]]]:=sta_pi1_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv1i.
      apply: dyn_sta_step...
      apply: dyn_app1...
      have:=sta_subst tyB (dyn_sta_type tyn).
      asimpl... }
    { exfalso.
      apply: sta_lam0_pi1_false...
      apply: dyn_sta_type... }
    { have[wf1 wf2]:=dyn_wf_merge mrg wf.
      have[x tyP]:=dyn_valid wf1 tym.
      have[_[tyA _]]:=sta_pi1_inv tyP.
      have [tym0[e1 e2]]:=dyn_lam1_inv wf1 tyP tym.
      subst. apply: dyn_subst1...
      apply: dyn_val_key... } }
Qed.

Corollary dyn_rd Γ Δ m n A :
  dyn_wf Γ Δ -> Γ ; Δ ⊢ m : A -> m ~>>* n -> Γ ; Δ ⊢ n : A.
Proof with eauto.
  move=>wf ty rd. elim: rd Γ A wf ty=>{n}...
  move=>n z rd ih st Γ A wf tym.
  have tyn:=ih _ _ wf tym.
  apply: dyn_sr...
Qed.
