From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_type :
  pstep Ty Ty
| pstep_forall A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Forall A B) (Forall A' B')
| pstep_arrow A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Arrow A B) (Arrow A' B')
| pstep_lam A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Lam A m) (Lam A' m')
| pstep_fun A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fun A m) (Fun A' m')
| pstep_inst m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (Inst m n) (Inst m' n')
| pstep_call m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (Call m n) (Call m' n')
| pstep_betaI A m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (Inst (Lam A m) n) (m'.[n'/])
| pstep_betaC A m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (Call (Fun A m) n) (m'.[n'/])
| pstep_unitT :
  pstep UnitT UnitT
| pstep_unit :
  pstep Unit Unit
| pstep_natT :
  pstep NatT NatT
| pstep_nat n :
  pstep (Nat n) (Nat n)
| pstep_rand m m' :
  pstep m m' ->
  pstep (Rand m) (Rand m').

Definition sred σ τ := forall x : var, (σ x) ~>* (τ x).

Lemma sta_step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using sta_step.
  { move=> A m n σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_step_betaI. autosubst. }
  { move=> A m n σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_step_betaC. autosubst. }
Qed.

Lemma sta_red_inst m m' n n' :
  m ~>* m' -> n ~>* n' -> Inst m n ~>* Inst m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Inst m' n)).
  apply: (star_hom (Inst^~ n)) r1=>x y. exact: sta_step_instL.
  apply: star_hom r2. exact: sta_step_instR.
Qed.

Lemma sta_red_call m m' n n' :
  m ~>* m' -> n ~>* n' -> Call m n ~>* Call m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Call m' n)).
  apply: (star_hom (Call^~ n)) r1=>x y. exact: sta_step_callL.
  apply: star_hom r2. exact: sta_step_callR.
Qed.

Lemma sta_red_lam A A' m m' :
  A ~>* A' -> m ~>* m' -> Lam A m ~>* Lam A' m'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam A' m)).
  apply: (star_hom (Lam^~ m)) r1=>x y. exact: sta_step_lamL.
  apply: (star_hom (Lam A')) r2=>x y. exact: sta_step_lamR.
Qed.

Lemma sta_red_fun A A' m m' :
  A ~>* A' -> m ~>* m' -> Fun A m ~>* Fun A' m'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Fun A' m)).
  apply: (star_hom (Fun^~ m)) r1=>x y. exact: sta_step_funL.
  apply: (star_hom (Fun A')) r2=>x y. exact: sta_step_funR.
Qed.

Lemma sta_red_forall A A' B B' :
  A ~>* A' -> B ~>* B' -> Forall A B ~>* Forall A' B'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Forall A' B)).
  apply: (star_hom (Forall^~ B)) r1=>x y. exact: sta_step_forallL.
  apply: (star_hom (Forall A')) r2=>x y. exact: sta_step_forallR.
Qed.

Lemma sta_red_arrow A A' B B' :
  A ~>* A' -> B ~>* B' -> Arrow A B ~>* Arrow A' B'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Arrow A' B)).
  apply: (star_hom (Arrow^~ B)) r1=>x y. exact: sta_step_arrowL.
  apply: (star_hom (Arrow A')) r2=>x y. exact: sta_step_arrowR.
Qed.

Lemma sta_red_rand m m' :
  m ~>* m' -> Rand m ~>* Rand m'.
Proof.
  move=> r. apply: (star_hom (Rand)) r=>x y. exact: sta_step_rand.
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

#[global] Hint Resolve
  sta_red_inst sta_red_call
  sta_red_lam sta_red_fun
  sta_red_forall sta_red_arrow
  sta_red_rand
  sred_up sred_upn : sta_red_congr.

Lemma sta_red_compat σ τ s : sred σ τ -> sta_red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 9 with sta_red_congr. Qed.

Definition sconv (σ τ : var -> term) := forall x, σ x === τ x.

Lemma sta_conv_inst m m' n n' :
  m === m' -> n === n' -> Inst m n === Inst m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Inst m' n)).
  apply: (conv_hom (Inst^~ n)) r1=>x y. exact: sta_step_instL.
  apply: conv_hom r2. exact: sta_step_instR.
Qed.

Lemma sta_conv_call m m' n n' :
  m === m' -> n === n' -> Call m n === Call m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Call m' n)).
  apply: (conv_hom (Call^~ n)) r1=>x y. exact: sta_step_callL.
  apply: conv_hom r2. exact: sta_step_callR.
Qed.

Lemma sta_conv_lam A A' m m' :
  A === A' -> m === m' -> Lam A m === Lam A' m'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam A' m)).
  apply: (conv_hom (Lam^~ m)) r1=>x y. exact: sta_step_lamL.
  apply: (conv_hom (Lam A')) r2=>x y. exact: sta_step_lamR.
Qed.

Lemma sta_conv_fun A A' m m' :
  A === A' -> m === m' -> Fun A m === Fun A' m'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Fun A' m)).
  apply: (conv_hom (Fun^~ m)) r1=>x y. exact: sta_step_funL.
  apply: (conv_hom ((Fun A'))) r2=>x y. exact: sta_step_funR.
Qed.

Lemma sta_conv_forall A A' B B' :
  A === A' -> B === B' -> Forall A B === Forall A' B'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Forall A' B)).
  apply: (conv_hom (Forall^~ B)) r1=>x y. exact: sta_step_forallL.
  apply: (conv_hom (Forall A')) r2=>x y. exact: sta_step_forallR.
Qed.

Lemma sta_conv_arrow A A' B B' :
  A === A' -> B === B' -> Arrow A B === Arrow A' B'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Arrow A' B)).
  apply: (conv_hom (Arrow^~ B)) r1=>x y. exact: sta_step_arrowL.
  apply: (conv_hom (Arrow A')) r2=>x y. exact: sta_step_arrowR.
Qed.

Lemma sta_conv_rand m m' :
  m === m' -> Rand m === Rand m'.
Proof.
  move=> r. apply: (conv_hom (Rand)) r=>x y. exact: sta_step_rand.
Qed.

Lemma sta_conv_subst σ m n :
  m === n -> m.[σ] === n.[σ].
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

#[export] Hint Resolve
  sta_conv_inst sta_conv_call
  sta_conv_lam sta_conv_fun
  sta_conv_forall sta_conv_arrow
  sta_conv_rand
  sconv_up sconv_upn : sta_conv_congr.

Lemma sta_conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 9 with sta_conv_congr. Qed.

Lemma sta_conv_beta m n1 n2 : n1 === n2 -> m.[n1/] === m.[n2/].
Proof. move=> c. by apply: sta_conv_compat => -[]. Qed.

Lemma pstep_reflexive m : pstep m m.
Proof. elim: m; eauto using pstep. Qed.
#[global] Hint Resolve pstep_reflexive.

Lemma sta_step_pstep m m' : sta_step m m' -> pstep m m'.
Proof with eauto using pstep, pstep_reflexive. elim... Qed.

Lemma pstep_sta_red m n : pstep m n -> m ~>* n.
Proof with eauto.
  elim=>{m n}//=; eauto with sta_red_congr.
  { move=> A m m' n n' p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n/])). exact: sta_red_subst.
    by apply: sta_red_compat=>-[|]. }
  { move=> A m m' n n' p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n/])). exact: sta_red_subst.
    by apply: sta_red_compat=>-[|]. }
Qed.

Lemma pstep_subst m n σ : pstep m n -> pstep m.[σ] n.[σ].
Proof with eauto using pstep, pstep_reflexive.
  move=>ps. elim: ps σ=>{m n}...
  { move=>A m m' n n' ps1 ih1 ps2 ih2 σ. asimpl.
    pose proof (pstep_betaI A.[σ] (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m m' n n' ps1 ih1 ps2 ih2 σ. asimpl.
    pose proof (pstep_betaC A.[σ] (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
Qed.

Definition psstep (σ τ : var -> term) := forall x, pstep (σ x) (τ x).

Lemma psstep_reflexive σ : psstep σ σ.
Proof with eauto using pstep_reflexive. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_reflexive.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma psstep_upn n σ τ : psstep σ τ -> psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ pss. by asimpl.
  move=>n ihn σ τ /ihn/psstep_up. by asimpl.
Qed.

Lemma pstep_compat m n σ τ :
  pstep m n -> psstep σ τ -> pstep m.[σ] n.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=> ps. elim: ps σ τ=>{m n}...
  { move=> A m m' n n' ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (pstep_betaI A.[σ] (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=> A m m' n n' ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (pstep_betaC A.[σ] (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep_compat, psstep_reflexive, psstep_compat.
  move...
Qed.

Lemma pstep_compat_beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using pstep_compat, psstep_reflexive, psstep_compat.
  move...
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 -> exists2 m', pstep m1 m' & pstep m2 m'.
Proof with eauto 6 using
  pstep, pstep_compat, pstep_compat_beta,
  psstep_compat, psstep_reflexive.
  move=>ps. elim: ps m2=>{m m1}...
  { move=>A A' B B' pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[B0 pB1 pB2]:=ihB _ H3.
    exists (Forall A0 B0)... }
  { move=>A A' B B' pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[B0 pB1 pB2]:=ihB _ H3.
    exists (Arrow A0 B0)... }
  { move=>A A' m m' pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[m0 pm1 pm2]:=ihm _ H3.
    exists (Lam A0 m0)... }
  { move=>A A' m m' pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[m0 pm1 pm2]:=ihm _ H3.
    exists (Fun A0 m0)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (Inst m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Lam A m0) (Lam A m'0)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... } }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (Call m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Fun A m0) (Fun A m'0)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... } }
  { move=>A m m' n n' pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H5.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H3.
      have[n0 pn1 pn2]:=ihn _ H4.
      exists (m0.[n0/])... } }
  { move=>A m m' n n' pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H5.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H3.
      have[n0 pn1 pn2]:=ihn _ H4.
      exists (m0.[n0/])... } }
  { move=>m m' pm ihm x p. inv p.
    have[m0 pm1 pm2]:=ihm _ H0.
    exists (Rand m0)... }
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> m ~>* m2 -> exists2 m', m1 ~>* m' & pstep m2 m'.
Proof with eauto using pstep_reflexive, star.
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

Lemma sta_red_var_inv x y : Var x ~>* y -> y = Var x.
Proof.
  elim=>//{} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma sta_red_ty_inv A :
  Ty ~>* A -> A = Ty.
Proof.
  elim=>//y z r1 e r2; subst.
  inv r2.
Qed.

Lemma sta_red_forall_inv A B x :
  Forall A B ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Forall A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_arrow_inv A B x :
  Arrow A B ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Arrow A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_lam_inv A m x :
  Lam A m ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam A' m'.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1[A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sta_red_fun_inv A m x :
  Fun A m ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Fun A' m'.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1[A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sta_red_unitT_inv x :
  UnitT ~>* x -> x = UnitT.
Proof.
  elim=>//.
  move=>y z rm e r. subst. inv r.
Qed.

Lemma sta_red_unit_inv x :
  Unit ~>* x -> x = Unit.
Proof.
  elim=>//.
  move=>y z rm e r. subst. inv r.
Qed.

Lemma sta_red_natT_inv x :
  NatT ~>* x -> x = NatT.
Proof.
  elim=>//.
  move=>y z rm e r. subst. inv r.
Qed.

Lemma sta_red_nat_inv n x :
  Nat n ~>* x -> x = Nat n.
Proof.
  elim=>//.
  move=>y z rm e r. subst. inv r.
Qed.

Lemma forall_inj A A' B B' :
  Forall A B === Forall A' B' -> A === A' /\ B === B'.
Proof.
  move/church_rosser=>
    [x/sta_red_forall_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_forall_inv[A2[B2[rA2[rB2[]]]]]] eA eB; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma arrow_inj A A' B B' :
  Arrow A B === Arrow A' B' -> A === A' /\ B === B'.
Proof.
  move/church_rosser=>
    [x/sta_red_arrow_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_arrow_inv[A2[B2[rA2[rB2[]]]]]] eA eB; subst.
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
  | Var    => apply sta_red_var_inv in H
  | Ty     => apply sta_red_ty_inv in H
  | Forall => apply sta_red_forall_inv in H
  | Arrow  => apply sta_red_arrow_inv in H
  | Lam    => apply sta_red_lam_inv in H
  | Fun    => apply sta_red_fun_inv in H
  | UnitT  => apply sta_red_unitT_inv in H
  | Unit   => apply sta_red_unit_inv in H
  | NatT   => apply sta_red_natT_inv in H
  | Nat    => apply sta_red_nat_inv in H
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
