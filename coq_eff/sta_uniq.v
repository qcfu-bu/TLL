From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_sort_uniq Γ s A : Γ ⊢ Sort s : A -> Sort U === A.
Proof with eauto.
  move e:(Sort s)=>n ty. elim: ty s e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB t e; subst.
  have eq':=ihm _ erefl.
  apply: conv_trans...
Qed.

Lemma sta_has_uniq Γ x A B : sta_has Γ x A -> sta_has Γ x B -> A = B.
Proof with eauto.
  move=>hs. elim: hs B=>{Γ x A}.
  { move=>Γ A B hs. inv hs... }
  { move=>Γ A B x hs ih C hs'. inv hs'.
    rewrite (ih _ H3)... }
Qed.

Lemma sta_var_uniq Γ A B x :
  Γ ⊢ Var x : B -> sta_has Γ x A -> A === B.
Proof with eauto.
  move e:(Var x)=>n ty. elim: ty A x e=>//{Γ n B}.
  { move=>Γ x A wf hs1 A0 x0 [e] hs2; subst.
    by rewrite (sta_has_uniq hs1 hs2). }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 x e hs; subst.
    have eq':=ihm _ _ erefl hs.
    apply: conv_trans... }
Qed.

Lemma sta_pi0_uniq Γ A B C s :
  Γ ⊢ Pi0 A B s : C -> Sort s === C.
Proof with eauto.
  move e:(Pi0 A B s)=>n ty. elim: ty A B s e=>//{Γ n C}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: conv_trans... }
Qed.

Lemma sta_pi1_uniq Γ A B C s :
  Γ ⊢ Pi1 A B s : C -> Sort s === C.
Proof with eauto.
  move e:(Pi1 A B s)=>n ty. elim: ty A B s e=>//{Γ n C}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: conv_trans... }
Qed.

Lemma sta_lam0_uniq Γ A B C m s :
  Γ ⊢ Lam0 A m s : C -> (forall C, (A :: Γ) ⊢ m : C -> B === C) -> Pi0 A B s === C.
Proof with eauto.
  move e:(Lam0 A m s)=>n ty. elim: ty A B m s e=>//{Γ n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] h; subst.
    have eq:=h _ tym. inv eq.
    econstructor.
    apply: sta_conv_pi0...
    apply: sta_conv_pi0... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e h; subst.
    have eq':=ihm _ _ _ _ erefl h.
    apply: conv_trans... }
Qed.

Lemma sta_lam1_uniq Γ A B C m s :
  Γ ⊢ Lam1 A m s : C -> (forall C, (A :: Γ) ⊢ m : C -> B === C) -> Pi1 A B s === C.
Proof with eauto.
  move e:(Lam1 A m s)=>n ty. elim: ty A B m s e=>//{Γ n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] h; subst.
    have eq:=h _ tym. inv eq.
    econstructor.
    apply: sta_conv_pi1...
    apply: sta_conv_pi1... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e h; subst.
    have eq':=ihm _ _ _ _ erefl h.
    apply: conv_trans... }
Qed.

Lemma sta_app0_uniq Γ A B C m n s :
  Γ ⊢ App m n : C -> (forall C, Γ ⊢ m : C -> Pi0 A B s === C) -> B.[n/] === C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have/pi0_inj[_[eq' _]]:=h _ tym.
    apply: sta_conv_subst... }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have eq:=h _ tym.
    exfalso. solve_conv. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: conv_trans... }
Qed.

Lemma sta_app1_uniq Γ A B C m n s :
  Γ ⊢ App m n : C -> (forall C, Γ ⊢ m : C -> Pi1 A B s === C) -> B.[n/] === C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have eq:=h _ tym.
    exfalso. solve_conv. }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have/pi1_inj[_[eq' _]]:=h _ tym.
    apply: sta_conv_subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: conv_trans... }
Qed.

Lemma sta_unit_uniq Γ A : Γ ⊢ Unit : A -> Sort U === A.
Proof with eauto.
  move e:(Unit)=>n ty. elim: ty e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  have eq':=ihm erefl.
  apply: conv_trans...
Qed.

Lemma sta_it_uniq Γ A : Γ ⊢ It : A -> Unit === A.
Proof with eauto.
  move e:(It)=>x ty. elim: ty e=>//{Γ x A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  have eq':=ihm erefl.
  apply: conv_trans...
Qed.

Lemma sta_nat_uniq Γ A : Γ ⊢ Nat : A -> Sort U === A.
Proof with eauto.
  move e:(Nat)=>n ty. elim: ty e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  have eq':=ihm erefl.
  apply: conv_trans...
Qed.

Lemma sta_num_uniq Γ n A : Γ ⊢ Num n : A -> Nat === A.
Proof with eauto.
  move e:(Num n)=>x ty. elim: ty n e=>//{Γ x A}.
  move=>Γ A B m s eq tym ihm tyB ihB n e; subst.
  have eq':=ihm _ erefl.
  apply: conv_trans...
Qed.

Lemma sta_rand_uniq Γ A : Γ ⊢ Rand : A -> Pi1 Unit (IO Nat) U === A.
Proof with eauto.
  move e:(Rand)=>x ty. elim: ty e=>//{Γ x A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  have eq':=ihm erefl.
  apply: conv_trans...
Qed.

Lemma sta_io_uniq Γ A B : Γ ⊢ IO A : B -> Sort L === B.
Proof with eauto.
  move e:(IO A)=>x ty. elim: ty A e=>//{Γ x B}.
  move=>Γ A B m s eq tym ihm tyB ihB A0 e; subst.
  have eq':=ihm _ erefl.
  apply: conv_trans...
Qed.

Lemma sta_return_uniq Γ m A B :
  Γ ⊢ Return m : B -> (forall B, Γ ⊢ m : B -> A === B) -> IO A === B.
Proof with eauto.
  move e:(Return m)=>x ty. elim: ty m A e=>//{Γ x B}.
  { move=>Γ m A tym ihm m0 A0[e]h; subst.
    have eq:=h _ tym. apply: sta_conv_io... }
  { move=>Γ A B m s eq tym ihm tyB ihB m0 A0 e h; subst.
    have eq':=ihm _ _ erefl h.
    apply: conv_trans... }
Qed.

Lemma sta_letin_uniq Γ m n A B C :
  Γ ⊢ LetIn m n : C ->
  Γ ⊢ m : IO A ->
  (forall A0, Γ ⊢ m : A0 -> IO A === A0) ->
  (forall B0, (A :: Γ) ⊢ n : B0 -> IO B.[ren (+1)] === B0) ->
  IO B === C.
Proof with eauto.
  move e:(LetIn m n)=>x ty. elim: ty m n e A B=>//{Γ x C}.
  { move=>Γ m n A B s tyB ihB tym ihm tyn ihn m0 n0[e1 e2]A0 B0 h1 h2 h3; subst.
    have[s0 tyI]:=sta_valid h1.
    have[s1[tyA0/sort_inj e]]:=sta_io_inv tyI. subst.
    have/io_inj eq1:=h2 _ tym.
    have/h3/io_inj eq2:=sta_ctx_conv eq1 tyA0 tyn.
    apply: sta_conv_io.
    pose proof (sta_conv_subst (ren (subn^~ 1)) eq2) as H.
    asimpl in H.
    replace ((+1) >>> subn_rec^~ 1) with (@id nat) in H.
    asimpl in H... unfold funcomp. f_ext=>//=. lia. }
  { move=>Γ A B m s eq tym ihm tyB ihB m0 n e A0 B0 h1 h2 h3; subst.
    apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma sta_uniq Γ m A B :
  Γ ⊢ m : A -> Γ ⊢ m : B -> A === B.
Proof with eauto.
  move=>ty. elim: ty B=>{Γ m A}.
  { move=>Γ s B tyB.
    apply: sta_sort_uniq... }
  { move=>Γ x A wf hs B ty.
    apply: sta_var_uniq... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    apply: sta_pi0_uniq... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    apply: sta_pi1_uniq... }
  { move=>Γ A B m s tym ihm B0 ty.
    apply: sta_lam0_uniq... }
  { move=>Γ A B m s tym ihm B0 ty.
    apply: sta_lam1_uniq... }
  { move=>Γ A B m n s tym ihm tyn ihn B0 ty.
    apply: sta_app0_uniq... }
  { move=>Γ A B m n s tym ihm tyn ihn B0 ty.
    apply: sta_app1_uniq... }
  { move=>Γ wf B ty.
    apply: sta_unit_uniq... }
  { move=>Γ wf B ty.
    apply: sta_it_uniq... }
  { move=>Γ wf B ty.
    apply: sta_nat_uniq... }
  { move=>Γ n wf B ty.
    apply: sta_num_uniq... }
  { move=>Γ wf B ty.
    apply: sta_rand_uniq... }
  { move=>Γ A s tyA ihA B ty.
    apply: sta_io_uniq... }
  { move=>Γ m A tym ihm B ty.
    apply: sta_return_uniq... }
  { move=>Γ m n A B s tyB ihB tym ihm tyn ihn B0 ty.
    apply: sta_letin_uniq... }
  { move=>Γ A B m s eq tym1 ihm tyB ihB B0 tym2.
    apply: conv_trans.
    apply: conv_sym...
    exact: ihm. }
Qed.
