From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort s :
  pstep (@s) (@s)
| pstep_pi0 A A' B B' s t :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi0 A B s t) (Pi0 A' B' s t)
| pstep_pi1 A A' B B' s t :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi1 A B s t) (Pi1 A' B' s t)
| pstep_lam0 A A' m m' s t :
  pstep A A' ->
  pstep m m' ->
  pstep (Lam0 A m s t) (Lam0 A' m' s t)
| pstep_lam1 A A' m m' s t :
  pstep A A' ->
  pstep m m' ->
  pstep (Lam1 A m s t) (Lam1 A' m' s t)
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta0 A m m' n n' s t :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam0 A m s t) n) (m'.[n'/])
| pstep_beta1 A m m' n n' s t :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam1 A m s t) n) (m'.[n'/])
| pstep_box : pstep Box Box.

Definition sred σ τ := forall x : var, (σ x) ~>* (τ x).

Lemma sta_step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using sta_step.
  { move=> A m n s t σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_beta0. autosubst. }
  { move=> A m n s t σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_beta1. autosubst. }
Qed.

Lemma sta_red_app m m' n n' :
  m ~>* m' -> n ~>* n' -> App m n ~>* App m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App m' n)).
  apply: (star_hom (App^~ n)) r1=>x y. exact: sta_appL.
  apply: star_hom r2. exact: sta_appR.
Qed.

Lemma sta_red_lam0 A A' m m' s t :
  A ~>* A' -> m ~>* m' -> Lam0 A m s t ~>* Lam0 A' m' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam0 A' m s t)).
  apply: (star_hom (((Lam0^~ m)^~ s)^~ t)) r1=>x y. exact: sta_lam0L.
  apply: (star_hom (((Lam0 A')^~ s)^~ t)) r2=>x y. exact: sta_lam0R.
Qed.

Lemma sta_red_lam1 A A' m m' s t :
  A ~>* A' -> m ~>* m' -> Lam1 A m s t ~>* Lam1 A' m' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam1 A' m s t)).
  apply: (star_hom (((Lam1^~ m)^~ s)^~ t)) r1=>x y. exact: sta_lam1L.
  apply: (star_hom (((Lam1 A')^~ s)^~ t)) r2=>x y. exact: sta_lam1R.
Qed.

Lemma sta_red_pi0 A A' B B' s t :
  A ~>* A' -> B ~>* B' -> Pi0 A B s t ~>* Pi0 A' B' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi0 A' B s t)).
  apply: (star_hom (((Pi0^~ B)^~ s)^~ t)) r1=>x y. exact: sta_pi0L.
  apply: (star_hom (((Pi0 A')^~ s)^~ t)) r2=>x y. exact: sta_pi0R.
Qed.

Lemma sta_red_pi1 A A' B B' s t :
  A ~>* A' -> B ~>* B' -> Pi1 A B s t ~>* Pi1 A' B' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi1 A' B s t)).
  apply: (star_hom (((Pi1^~ B)^~ s)^~ t)) r1=>x y. exact: sta_pi1L.
  apply: (star_hom (((Pi1 A')^~ s)^~ t)) r2=>x y. exact: sta_pi1R.
Qed.

Lemma sta_red_subst m n σ : m ~>* n -> m.[σ] ~>* n.[σ].
Proof.
  move=>st.
  elim: st σ=>{n}; eauto.
  move=> n n' r ih st σ.
  move:(ih σ)=>{}ih.
  move:(sta_step_subst σ st)=>r'.
  apply: star_trans.
  apply: ih.
  by apply: star1.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: sta_red_subst. exact: A. Qed.

Lemma sred_upn n σ τ : sred σ τ -> sred (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sred_up. by asimpl.
Qed.

Hint Resolve
  sta_red_app
  sta_red_lam0 sta_red_lam1
  sta_red_pi0 sta_red_pi1
  sred_up sred_upn : sta_red_congr.

Lemma sta_red_compat σ τ s : sred σ τ -> sta_red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with sta_red_congr. Qed.

Definition sconv (σ τ : var -> term) := forall x, σ x === τ x.

Lemma sta_conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (App m' n)).
  apply: (conv_hom (App^~ n)) r1=>x y. exact: sta_appL.
  apply: conv_hom r2. exact: sta_appR.
Qed.

Lemma sta_conv_lam0 A A' m m' s t :
  A === A' -> m === m' -> Lam0 A m s t === Lam0 A' m' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam0 A' m s t)).
  apply: (conv_hom (((Lam0^~ m)^~ s)^~ t)) r1=>x y. exact: sta_lam0L.
  apply: (conv_hom (((Lam0 A')^~ s)^~ t)) r2=>x y. exact: sta_lam0R.
Qed.

Lemma sta_conv_lam1 A A' m m' s t :
  A === A' -> m === m' -> Lam1 A m s t === Lam1 A' m' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam1 A' m s t)).
  apply: (conv_hom (((Lam1^~ m)^~ s)^~ t)) r1=>x y. exact: sta_lam1L.
  apply: (conv_hom (((Lam1 A')^~ s)^~ t)) r2=>x y. exact: sta_lam1R.
Qed.

Lemma sta_conv_pi0 A A' B B' s t :
  A === A' -> B === B' -> Pi0 A B s t === Pi0 A' B' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi0 A' B s t)).
  apply: (conv_hom (((Pi0^~ B)^~ s)^~ t)) r1=>x y. exact: sta_pi0L.
  apply: (conv_hom (((Pi0 A')^~ s)^~ t)) r2=>x y. exact: sta_pi0R.
Qed.

Lemma sta_conv_pi1 A A' B B' s t :
  A === A' -> B === B' -> Pi1 A B s t === Pi1 A' B' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi1 A' B s t)).
  apply: (conv_hom (((Pi1^~ B)^~ s)^~ t)) r1=>x y. exact: sta_pi1L.
  apply: (conv_hom (((Pi1 A')^~ s)^~ t)) r2=>x y. exact: sta_pi1R.
Qed.

Lemma sta_conv_subst σ s t :
  s === t -> s.[σ] === t.[σ].
Proof.
  move=>c.
  apply: conv_hom c.
  exact: sta_step_subst.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: sta_conv_subst. Qed.

Lemma sconv_upn n σ τ : sconv σ τ -> sconv (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sconv_up. by asimpl.
Qed.

Hint Resolve
  sta_conv_app
  sta_conv_lam0 sta_conv_lam1
  sta_conv_pi0 sta_conv_pi1
  sconv_up sconv_upn : sta_conv_congr.

Lemma sta_conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with sta_conv_congr. Qed.

Lemma sta_conv_beta m n1 n2 : n1 === n2 -> m.[n1/] === m.[n2/].
Proof. move=> c. by apply: sta_conv_compat => -[]. Qed.

Lemma pstep_refl m : pstep m m.
Proof. elim: m; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma sta_step_pstep m m' : sta_step m m' -> pstep m m'.
Proof with eauto using pstep, pstep_refl. elim... Qed.

Lemma pstep_sta_red m n : pstep m n -> m ~>* n.
Proof.
  elim=>{m n}//=; eauto with sta_red_congr.
  { move=> A m m' n n' s t p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n.:Var])). exact: sta_red_subst.
    by apply: sta_red_compat => -[|]. }
  { move=> A m m' n n' s t p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n.:Var])). exact: sta_red_subst.
    by apply: sta_red_compat => -[|]. }
Qed.

Lemma pstep_subst m n σ : pstep m n -> pstep m.[σ] n.[σ].
Proof with eauto using pstep, pstep_refl.
  move=>ps. elim: ps σ=>{m n}...
  { move=>A m m' n n' s t ps1 ih1 ps2 ih2 σ.
    asimpl.
    pose proof (pstep_beta0 A.[σ] s t (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m m' n n' s t ps1 ih1 ps2 ih2 σ.
    asimpl.
    pose proof (pstep_beta1 A.[σ] s t (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
Qed.

Definition psstep (σ τ : var -> term) := forall x, pstep (σ x) (τ x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma psstep_upn n σ τ : psstep σ τ -> psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ pss. by asimpl.
  move=>n ihn σ τ /ihn/psstep_up. by asimpl.
Qed.

Lemma pstep_compat s t σ τ :
  pstep s t -> psstep σ τ -> pstep s.[σ] t.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=> ps. elim: ps σ τ=>{s t}...
  { move=> A m m' n n' s t ps1 ih1 ps2 ih2 σ τ pss.
    asimpl.
    pose proof (pstep_beta0 A.[σ] s t (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=> A m m' n n' s t ps1 ih1 ps2 ih2 σ τ pss.
    asimpl.
    pose proof (pstep_beta1 A.[σ] s t (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat.
  move...
Qed.

Lemma pstep_compat_beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat.
  move...
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 -> exists2 m', pstep m1 m' & pstep m2 m'.
Proof with eauto 6 using
  pstep, pstep_refl,
  pstep_compat, pstep_compat_beta,
  psstep_compat, psstep_refl.
  move=>ps. elim: ps m2=>{m m1}...
  { move=>A A' B B' s t pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H4.
    have[B0 pB1 pB2]:=ihB _ H5.
    exists (Pi0 A0 B0 s t)... }
  { move=>A A' B B' s t pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H4.
    have[B0 pB1 pB2]:=ihB _ H5.
    exists (Pi1 A0 B0 s t)... }
  { move=>A A' m m' s t pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H4.
    have[m0 pm1 pm2]:=ihm _ H5.
    exists (Lam0 A0 m0 s t)... }
  { move=>A A' m m' s t pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H4.
    have[m0 pm1 pm2]:=ihm _ H5.
    exists (Lam1 A0 m0 s t)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (App m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Lam0 A m0 s t) (Lam0 A m'0 s t)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Lam1 A m0 s t) (Lam1 A m'0 s t)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... } }
  { move=>A m m' n n' s t pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H7.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H5.
      have[n0 pn1 pn2]:=ihn _ H6.
      exists (m0.[n0/])... } }
  { move=>A m m' n n' s t pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H7.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H5.
      have[n0 pn1 pn2]:=ihn _ H6.
      exists (m0.[n0/])... } }
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> m ~>* m2 -> exists2 m', m1 ~>* m' & pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>m1 m2 r1 ih /sta_step_pstep p1 m' p2.
  move:(ih _ p2)=>[m3 r2 p3].
  move:(pstep_diamond p1 p3)=>[m4 p4 p5].
  exists m4...
  apply: star_trans.
  apply: r2.
  by apply: pstep_sta_red.
Qed.

Theorem confluence :
  confluent sta_step.
Proof with eauto using sta_step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r.
  elim: r z=>{y}.
  move=>z r. exists z...
  move=>y z r1 ih /sta_step_pstep p z0 /ih[z1 r2 r3].
  move:(strip p r2)=>[z2 r4 p1].
  exists z2...
  apply: star_trans.
  apply r3.
  apply: pstep_sta_red...
Qed.

Theorem church_rosser :
  CR sta_step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma sta_red_sort_inv s A :
  @s ~>* A -> A = @s.
Proof.
  elim=>//y z r1 e r2; subst.
  inv r2.
Qed.

Lemma sta_red_pi0_inv A B s r x :
  Pi0 A B s r ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi0 A' B' s r.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd [A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_pi1_inv A B s r x :
  Pi1 A B s r ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi1 A' B' s r.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd [A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_var_inv x y : Var x ~>* y -> y = Var x.
Proof.
  elim=>//{} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma sta_red_lam0_inv A m x s t :
  Lam0 A m s t ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam0 A' m' s t.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sta_red_lam1_inv A m x s t :
  Lam1 A m s t ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam1 A' m' s t.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sort_inj s1 s2 :
  @s1 === @s2 -> s1 = s2.
Proof.
  move/church_rosser=>[x/sta_red_sort_inv->/sta_red_sort_inv[->]]//.
Qed.

Lemma pi0_inj A A' B B' s s' t t' :
  Pi0 A B s t === Pi0 A' B' s' t' ->
    A === A' /\ B === B' /\ s = s' /\ t = t'.
Proof.
  move/church_rosser=>
    [x/sta_red_pi0_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_pi0_inv[A2[B2[rA2[rB2[]]]]]] eA eB es et; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma pi1_inj A A' B B' s s' t t' :
  Pi1 A B s t === Pi1 A' B' s' t' ->
    A === A' /\ B === B' /\ s = s' /\ t = t'.
Proof.
  move/church_rosser=>
    [x/sta_red_pi1_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_pi1_inv[A2[B2[rA2[rB2[]]]]]] eA eB es et; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Ltac red_inv m H :=
  match m with
  | Var  => apply sta_red_var_inv in H
  | Sort => apply sta_red_sort_inv in H
  | Pi0  => apply sta_red_pi0_inv in H
  | Pi1  => apply sta_red_pi1_inv in H
  | Lam0 => apply sta_red_lam0_inv in H
  | Lam1 => apply sta_red_lam1_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : sta_red (?m _) _ |- _ ]         => red_inv m H
  | [ H : sta_red (?m _ _) _ |- _ ]       => red_inv m H
  | [ H : sta_red (?m _ _ _) _ |- _ ]     => red_inv m H
  | [ H : sta_red (?m _ _ _ _) _ |- _ ]   => red_inv m H
  | [ H : sta_red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : sta_red ?m _ |- _ ]             => red_inv m H
  end;
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  end; eauto.
