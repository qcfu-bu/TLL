From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive head_sim : term -> term -> Prop :=
| head_sim_var x : head_sim (Var x) (Var x)
| head_sim_sort s : head_sim (Sort s) (Sort s)
| head_sim_pi0 A1 A2 B1 B2 s :
  head_sim B1 B2 ->
  head_sim (Pi0 A1 B1 s) (Pi0 A2 B2 s)
| head_sim_pi1 A1 A2 B1 B2 s :
  head_sim B1 B2 ->
  head_sim (Pi1 A1 B1 s) (Pi1 A2 B2 s)
| head_sim_lam0 A m s : head_sim (Lam0 A m s) (Lam0 A m s)
| head_sim_lam1 A m s : head_sim (Lam1 A m s) (Lam1 A m s)
| head_sim_app m n : head_sim (App m n) (App m n)
| head_sim_sig0 A1 A2 B1 B2 s1 s2 :
  head_sim (Sig0 A1 B1 s1) (Sig0 A2 B2 s2)
| head_sim_sig1 A1 A2 B1 B2 s1 s2 :
  head_sim (Sig1 A1 B1 s1) (Sig1 A2 B2 s2)
| head_sim_pair0 m n t : head_sim (Pair0 m n t) (Pair0 m n t)
| head_sim_pair1 m n t : head_sim (Pair1 m n t) (Pair1 m n t)
| head_sim_letin A m n : head_sim (LetIn A m n) (LetIn A m n)
| head_sim_fix A m : head_sim (Fix A m) (Fix A m)
| head_sim_unit : head_sim Unit Unit
| head_sim_ii : head_sim II II
| head_sim_bool : head_sim Bool Bool
| head_sim_tt : head_sim TT TT
| head_sim_ff : head_sim FF FF
| head_sim_ifte A m n1 n2 : head_sim (Ifte A m n1 n2) (Ifte A m n1 n2)
| head_sim_io A B : head_sim (IO A) (IO B)
| head_sim_return m : head_sim (Return m) (Return m)
| head_sim_bind m n : head_sim (Bind m n) (Bind m n)
| head_sim_proto : head_sim Proto Proto
| head_sim_stop r : head_sim (Stop r) (Stop r)
| head_sim_act0 r A B : head_sim (Act0 r A B) (Act0 r A B)
| head_sim_act1 r A B : head_sim (Act1 r A B) (Act1 r A B)
| head_sim_ch r1 r2 A1 A2 : head_sim (Ch r1 A1) (Ch r2 A2)
| head_sim_cvar x : head_sim (CVar x) (CVar x)
| head_sim_fork A m : head_sim (Fork A m) (Fork A m)
| head_sim_recv0 m : head_sim (Recv0 m) (Recv0 m)
| head_sim_recv1 m : head_sim (Recv1 m) (Recv1 m)
| head_sim_send0 m : head_sim (Send0 m) (Send0 m)
| head_sim_send1 m : head_sim (Send1 m) (Send1 m)
| head_sim_close m : head_sim (Close m) (Close m)
| head_sim_wait m : head_sim (Wait m) (Wait m).

Inductive sim (m n : term) : Prop :=
| Sim x y : m === x -> head_sim x y -> y === n -> sim m n.

Inductive sta_ctx_sim : sta_ctx -> sta_ctx -> Prop :=
| sta_ctx_sim_nil : sta_ctx_sim nil nil
| sta_ctx_sim_ty A B Γ1 Γ2 :
  sim A B ->
  sta_ctx_sim Γ1 Γ2 ->
  sta_ctx_sim (A :: Γ1) (B :: Γ2).

Lemma head_sim_reflexive m : head_sim m m.
Proof with eauto using head_sim. elim: m... Qed.
Hint Resolve head_sim_reflexive.

Lemma head_sim_sym m n : head_sim m n -> head_sim n m.
Proof with eauto using head_sim. elim... Qed.

Lemma head_sim_subst m1 m2 σ : head_sim m1 m2 -> head_sim m1.[σ] m2.[σ].
Proof with eauto using head_sim.
  move=>hs. elim: hs σ=>{m1 m2}...
Qed.

Lemma sim_reflexive m : sim m m.
Proof with eauto. econstructor... Qed.
Hint Resolve sim_reflexive.

Lemma sim_transL x y z : sim x y -> y === z -> sim x z.
Proof with eauto.
  move=>sm eq. inv sm.
  econstructor...
  apply: conv_trans...
Qed.

Lemma sim_transR x y z : sim x y -> z === x -> sim z y.
Proof with eauto using head_sim.
  move=>sm eq. inv sm.
  econstructor.
  apply: conv_trans...
  apply: H0.
  apply: H1.
Qed.

Lemma sim_sym x y : sim x y -> sim y x.
Proof with eauto using head_sim.
  move=>sm. inv sm.
  have{}H:=conv_sym H.
  have{}H1:=conv_sym H1.
  have{}H0:=head_sim_sym H0.
  econstructor...
Qed.

Lemma sim_subst x y σ : sim x y -> sim x.[σ] y.[σ].
Proof with eauto.
  move=>sm. inv sm.
  econstructor.
  apply: sta_conv_subst...
  apply: head_sim_subst...
  apply: sta_conv_subst...
Qed.

Lemma sta_ctx_sim_sym Γ1 Γ2 : sta_ctx_sim Γ1 Γ2 -> sta_ctx_sim Γ2 Γ1.
Proof with eauto using sim_sym, sta_ctx_sim. elim... Qed.

Lemma sta_ctx_sim_reflexive Γ : sta_ctx_sim Γ Γ.
Proof with eauto using sta_ctx_sim. elim: Γ... Qed.
Hint Resolve sta_ctx_sim_reflexive.

Ltac solve_sim :=
  match goal with
  | [ H : sim _ _ |- _ ] => inv H
  end;
  match goal with
  | [ H : head_sim _ _ |- _ ] => inv H
  end;
  try solve[solve_conv];
  match goal with
  | [ eq1 : ?x === ?z, eq2 : ?z === ?y |- _ ] =>
    pose proof (conv_trans _ eq1 eq2); solve_conv
  end.

Lemma sim_sort s t : sim (Sort s) (Sort t) -> s = t.
Proof with eauto.
  move e1:(Sort s)=>m.
  move e2:(Sort t)=>n sm.
  inv sm.
  elim: H0 s t H H1=>//{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>s r t/sort_inj->/sort_inj->//. }
  { move=>m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n1 n2 s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
Qed.

Lemma sim_pi0_inj A1 A2 B1 B2 s1 s2 :
  sim (Pi0 A1 B1 s1) (Pi0 A2 B2 s2) ->
  sim B1 B2 /\ s1 = s2.
Proof with eauto using sim.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>A1 A2 B1 B2 s hB ihB A0 A3 B0 B3 s1 s2
      /pi0_inj[eqA1[eqB1 e1]]/pi0_inj[eqA2[eqB2 e2]]; subst.
    repeat split... }
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n1 n2 A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
Qed.

Lemma sim_pi1_inj A1 A2 B1 B2 s1 s2 :
  sim (Pi1 A1 B1 s1) (Pi1 A2 B2 s2) ->
  sim B1 B2 /\ s1 = s2.
Proof with eauto using sim.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>A1 A2 B1 B2 s hB ihB A0 A3 B0 B3 s1 s2
      /pi1_inj[eqA1[eqB1 e1]]/pi1_inj[eqA2[eqB2 e2]]; subst.
    repeat split... }
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n1 n2 A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
Qed.

Lemma sim_act0_inj A1 A2 B1 B2 r1 r2 :
  sim (Act0 r1 A1 B1) (Act0 r2 A2 B2) ->
    A1 === A2 /\ B1 === B2 /\  r1 = r2.
Proof with eauto.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 r1 r2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>m n A1 A2 B1 B2 r1 r2 eq1 eq2.
    have/act0_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n A1 A2 B1 B2 r1 r2 eq1 eq2.
    have/act0_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m A1 A2 B1 B2 r1 r2 eq1 eq2.
    have/act0_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n1 n2 A1 A2 B1 B2 r1 r2 eq1 eq2.
    have/act0_inj//:=conv_trans _ eq1 eq2. }
  { move=>m n A1 A2 B1 B2 r1 r2 eq1 eq2.
    have/act0_inj//:=conv_trans _ eq1 eq2. }
  { move=>r A B A1 A2 B1 B2 r1 r2 eq1 eq2.
    have/act0_inj//:=conv_trans _ eq1 eq2. }
Qed.

Lemma sta_sort_uniq Γ s A :
  Γ ⊢ Sort s : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Sort s)=>n ty. elim: ty s e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB t e; subst.
  have eq':=ihm _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_has_uniq Γ1 Γ2 x A B :
  sta_has Γ1 x A -> sta_has Γ2 x B -> sta_ctx_sim Γ1 Γ2 -> sim A B.
Proof with eauto.
  move=>hs. elim: hs Γ2 B=>{Γ1 x A}.
  { move=>Γ A Γ2 B hs csm. inv hs. inv csm. by apply: sim_subst. }
  { move=>Γ A B x hs ih Γ2 C hs' csm. inv hs'. inv csm.
    apply: sim_subst.
    apply: ih... }
Qed.

Lemma sta_var_uniq Γ1 Γ2 A B x :
  Γ1 ⊢ Var x : B -> sta_has Γ2 x A -> sta_ctx_sim Γ1 Γ2 -> sim A B.
Proof with eauto using sim_reflexive.
  move e:(Var x)=>n ty. elim: ty A x e Γ2=>//{Γ1 n B}.
  { move=>Γ1 x A wf hs1 A0 x0 [e] Γ2 hs2 csm; subst.
    have sm:=(sta_has_uniq hs1 hs2 csm)...
    apply: sim_sym... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 x e Γ2 hs csm; subst.
    have eq':=ihm _ _ erefl _ hs csm.
    apply: sim_transL... }
Qed.

Lemma sta_lam0_uniq Γ1 Γ2 A B C m s :
  Γ2 ⊢ Lam0 A m s : C ->
  (forall Γ2 C, Γ2 ⊢ m : C -> sta_ctx_sim (A :: Γ1) Γ2 -> sim B C) ->
  sta_ctx_sim Γ1 Γ2 ->
  sim (Pi0 A B s) C.
Proof with eauto.
  move e:(Lam0 A m s)=>n ty. elim: ty A B m s e Γ1=>//{Γ2 n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] Γ1 h csm; subst.
    have eq:=h _ _ tym (sta_ctx_sim_ty (sim_reflexive _) csm). inv eq.
    econstructor. apply: sta_conv_pi0...
    constructor... apply: sta_conv_pi0... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e Γ1 h csm; subst.
    have eq':=ihm _ _ _ _ erefl _ h csm.
    apply: sim_transL... }
Qed.

Lemma sta_pi0_uniq Γ A B C s :
  Γ ⊢ Pi0 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Pi0 A B s)=>n ty. elim: ty A B s e=>//{Γ n C}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_pi1_uniq Γ A B C s :
  Γ ⊢ Pi1 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Pi1 A B s)=>n ty. elim: ty A B s e=>//{Γ n C}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_lam1_uniq Γ1 Γ2 A B C m s :
  Γ2 ⊢ Lam1 A m s : C ->
  (forall Γ2 C, Γ2 ⊢ m : C -> sta_ctx_sim (A :: Γ1) Γ2 -> sim B C) ->
  sta_ctx_sim Γ1 Γ2 ->
  sim (Pi1 A B s) C.
Proof with eauto.
  move e:(Lam1 A m s)=>n ty. elim: ty A B m s e Γ1=>//{Γ2 n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] Γ1 h csm; subst.
    have eq:=h _ _ tym (sta_ctx_sim_ty (sim_reflexive _) csm). inv eq.
    econstructor. apply: sta_conv_pi1...
    constructor... apply: sta_conv_pi1... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e Γ1 h csm; subst.
    have eq':=ihm _ _ _ _ erefl _ h csm.
    apply: sim_transL... }
Qed.

Lemma sta_app_uniq Γ A B C m n s :
  Γ ⊢ App m n : C ->
  (forall C, Γ ⊢ m : C -> sim (Pi0 A B s) C \/ sim (Pi1 A B s) C) -> sim B.[n/] C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have[/sim_pi0_inj[eq' _]|eq']:=h _ tym.
    apply: sim_subst...
    exfalso. solve_sim. }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have[eq'|/sim_pi1_inj[eq' _]]:=h _ tym.
    exfalso. solve_sim.
    apply: sim_subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_sig0_uniq Γ A B C s :
  Γ ⊢ Sig0 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Sig0 A B s)=>m ty. elim: ty A B s e=>//{Γ m C}.
  { move=>Γ A B s r t ord tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_sig1_uniq Γ A B C s :
  Γ ⊢ Sig1 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Sig1 A B s)=>m ty. elim: ty A B s e=>//{Γ m C}.
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_pair0_uniq Γ A B C m n s :
  Γ ⊢ Pair0 m n s : C ->
  (forall X Y, Γ ⊢ m : X -> Γ ⊢ n : Y -> sim A X /\ sim B.[m/] Y) ->
  sim (Sig0 A B s) C.
Proof with eauto.
  move e:(Pair0 m n s)=>x ty. elim: ty A B m n s e=>//{Γ C x}.
  { move=>*.
    econstructor. eauto.
    constructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_pair1_uniq Γ A B C m n s :
  Γ ⊢ Pair1 m n s : C ->
  (forall X Y, Γ ⊢ m : X -> Γ ⊢ n : Y -> sim A X /\ sim B.[m/] Y) ->
  sim (Sig1 A B s) C.
Proof with eauto.
  move e:(Pair1 m n s)=>x ty. elim: ty A B m n s e=>//{Γ C x}.
  { move=>*.
    econstructor. eauto.
    constructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_letin_uniq Γ m n A B :
  Γ ⊢ LetIn A m n : B -> sim A.[m/] B.
Proof with eauto.
  move e:(LetIn A m n)=>x ty. elim: ty A m n e=>//{Γ B x}.
  { move=>Γ A B C m n s t
      tyC ihC tym ihm tyn ihn A0 m0 n0[e1 e2 e3]; subst... }
  { move=>Γ A B C m n s t
      tyC ihC tym ihm tyn ihn A0 m0 n0[e1 e2 e3]; subst... }
  { move=>Γ A B m s k tym ihm tyB _ A0 m0 n e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_fix_uniq Γ A B m : Γ ⊢ Fix A m : B -> sim A B.
Proof with eauto.
  move e:(Fix A m)=>n ty. elim: ty A m e=>//{Γ B n}.
  move=>Γ A m tym ihm A0 m0[e1 e2]; subst...
  move=>Γ A B m s eq tym ihm tyB ihB A0 m0 e; subst.
  { have eq':=ihm _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_unit_uniq Γ A : Γ ⊢ Unit : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Unit)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma sta_ii_uniq Γ A : Γ ⊢ II : A -> sim Unit A.
Proof with eauto.
  move e:(II)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma sta_bool_uniq Γ A : Γ ⊢ Bool : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Bool)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma sta_tt_uniq Γ A : Γ ⊢ TT : A -> sim Bool A.
Proof with eauto.
  move e:(TT)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma sta_ff_uniq Γ A : Γ ⊢ FF : A -> sim Bool A.
Proof with eauto.
  move e:(FF)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma sta_ifte_uniq Γ m n1 n2 A B :
  Γ ⊢ Ifte A m n1 n2 : B -> sim A.[m/] B.
Proof with eauto.
  move e:(Ifte A m n1 n2)=>x ty. elim: ty A m n1 n2 e=>//{Γ B x}.
  { move=>Γ m n1 n2 A s tym _ tyA _ tyn1 _ tyn2 _
      A0 m0 n0 n3[e1 e2 e3 e4]; subst.
    apply: sim_reflexive. }
  { move=>Γ A B m s eq tym ihm tyB _ A0 m0 n1 n2 e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_io_uniq Γ A B : Γ ⊢ IO A : B -> sim (Sort L) B.
Proof with eauto.
  move e:(IO A)=>x ty. elim: ty A e=>//{Γ x B}.
  move=>Γ A B m s eq tym ihm tyB ihB A0 e; subst.
  have eq':=ihm _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_return_uniq Γ m A B :
  Γ ⊢ Return m : B -> sim (IO A) B.
Proof with eauto.
  move e:(Return m)=>x ty. elim: ty m A e=>//{Γ x B}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB m0 A0 e; subst.
    have eq':=ihm _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_bind_uniq Γ m n A B :
  Γ ⊢ Bind m n : B -> sim (IO A) B.
Proof with eauto.
  move e:(Bind m n)=>x ty. elim: ty m n e A=>//{Γ x B}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB m0 n e A0; subst.
    have eq':=ihm _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_proto_uniq Γ B :
  Γ ⊢ Proto : B -> sim (Sort U) B.
Proof with eauto.
  move e:(Proto)=>x ty. elim: ty e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ e; subst.
  have eq':=ih erefl.
  apply: sim_transL...
Qed.

Lemma sta_stop_uniq Γ B r :
  Γ ⊢ Stop r : B -> sim (Proto) B.
Proof with eauto.  
  move e:(Stop r)=>x ty. elim: ty r e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ r e; subst.
  have eq':=ih _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_act0_uniq Γ A B C r :
  Γ ⊢ Act0 r A B : C -> sim (Proto) C.
Proof with eauto.  
  move e:(Act0 r A B)=>x ty. elim: ty A B r e=>//{Γ x C}.
  move=>Γ A B m s eq tym ihm tyB A0 B0 s0 r e; subst.
  have eq':=ihm _ _ _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_act1_uniq Γ A B C r :
  Γ ⊢ Act1 r A B : C -> sim (Proto) C.
Proof with eauto.  
  move e:(Act1 r A B)=>x ty. elim: ty A B r e=>//{Γ x C}.
  move=>Γ A B m s eq tym ihm tyB A0 B0 s0 r e; subst.
  have eq':=ihm _ _ _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_ch_uniq Γ A B r :
  Γ ⊢ Ch r A : B -> sim (Sort L) B.
Proof with eauto.
  move e:(Ch r A)=>x ty. elim: ty r A e=>//{Γ x B}.
  move=>Γ A B m s eq tym ihm tyB _ r A0 e; subst.
  have eq':=ihm _ _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_cvar_uniq Γ r x A B :
  Γ ⊢ CVar x : B -> sim (Ch r A) B.
Proof with eauto.
  move e:(CVar x)=>m ty. elim: ty r x A e=>//{Γ m B}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB r x A0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_fork_uniq Γ m A B :
  Γ ⊢ Fork A m : B -> sim (IO (Ch false A)) B.
Proof with eauto.
  move e:(Fork A m)=>x ty. elim: ty A m e=>//{Γ x B}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 m0 e; subst.
    have eq':=ihm _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_recv0_uniq Γ m A B C r :
  Γ ⊢ Recv0 m : C -> sim (IO (Sig0 A (Ch r B) L)) C.
Proof with eauto.
  move e:(Recv0 m)=>x ty. elim: ty A B m r e=>//{Γ x C}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 r e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_recv1_uniq Γ m A B C r :
  Γ ⊢ Recv1 m : C -> sim (IO (Sig1 A (Ch r B) L)) C.
Proof with eauto.
  move e:(Recv1 m)=>x ty. elim: ty A B m r e=>//{Γ x C}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 r e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_send0_uniq Γ m A B C r :
  Γ ⊢ Send0 m : C → sim (Pi0 A (IO (Ch r B)) L) C.
Proof with eauto.
  move e:(Send0 m)=>x ty. elim: ty A B m r e=>//{Γ x C}.
  { move=>Γ r1 r2 A B m xor tym ihm A0 B0 m0 r[e]; subst.
    econstructor. eauto.
    apply: head_sim_pi0. apply: A.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 r e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_send1_uniq Γ m A B C r :
  Γ ⊢ Send1 m : C → sim (Pi1 A (IO (Ch r B)) L) C.
Proof with eauto.
  move e:(Send1 m)=>x ty. elim: ty A B m r e=>//{Γ x C}.
  { move=>Γ r1 r2 A B m xor tym ihm A0 B0 m0 r[e]; subst.
    econstructor. eauto.
    apply: head_sim_pi1. apply: A.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 r e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_wait_uniq Γ m A :
  Γ ⊢ Wait m : A -> sim (IO Unit) A.
Proof with eauto.
  move e:(Wait m)=>x ty. elim: ty m e=>//{Γ x A}.
  move=>Γ A B m s eq tym ihm tyB ihB m0 e; subst.
  have eq':=ihm _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_close_uniq Γ m A :
  Γ ⊢ Close m : A -> sim (IO Unit) A.
Proof with eauto.
  move e:(Close m)=>x ty. elim: ty m e=>//{Γ x A}.
  move=>Γ A B m s eq tym ihm tyB ihB m0 e; subst.
  have eq':=ihm _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_uniq Γ1 Γ2 m A B :
  Γ1 ⊢ m : A -> Γ2 ⊢ m : B -> sta_ctx_sim Γ1 Γ2 -> sim A B.
Proof with eauto using sta_ctx_sim_sym.
  move=>ty. elim: ty Γ2 B=>{Γ1 m A}.
  { move=>*. apply: sta_sort_uniq... }
  { move=>*. apply: sta_var_uniq... }
  { move=>*. apply: sta_pi0_uniq... }
  { move=>*. apply: sta_pi1_uniq... }
  { move=>*. apply: sta_lam0_uniq... }
  { move=>*. apply: sta_lam1_uniq... }
  { move=>*. apply: sta_app_uniq... }
  { move=>*. apply: sta_app_uniq... }
  { move=>*. apply: sta_sig0_uniq... }
  { move=>*. apply: sta_sig1_uniq... }
  { move=>*. apply: sta_pair0_uniq... }
  { move=>*. apply: sta_pair1_uniq... }
  { move=>*. apply: sta_letin_uniq... }
  { move=>*. apply: sta_letin_uniq... }
  { move=>*. apply: sta_fix_uniq... }
  { move=>*. apply: sta_unit_uniq... }
  { move=>*. apply: sta_ii_uniq... }
  { move=>*. apply: sta_bool_uniq... }
  { move=>*. apply: sta_tt_uniq... }
  { move=>*. apply: sta_ff_uniq... }
  { move=>*. apply: sta_ifte_uniq... }
  { move=>*. apply: sta_io_uniq... }
  { move=>*. apply: sta_return_uniq... }
  { move=>*. apply: sta_bind_uniq... }
  { move=>*. apply: sta_proto_uniq... }
  { move=>*. apply: sta_stop_uniq... }
  { move=>*. apply: sta_act0_uniq... }
  { move=>*. apply: sta_act1_uniq... }
  { move=>*. apply: sta_ch_uniq... }
  { move=>*. apply: sta_cvar_uniq... }
  { move=>*. apply: sta_fork_uniq... }
  { move=>*. apply: sta_recv0_uniq... }
  { move=>*. apply: sta_recv1_uniq... }
  { move=>*. apply: sta_send0_uniq... }
  { move=>*. apply: sta_send1_uniq... }
  { move=>*. apply: sta_wait_uniq... }
  { move=>*. apply: sta_close_uniq... }
  { move=>Γ A B m s eq tym1 ihm tyB ihB Γ2 csm B0 tym2.
    apply: sim_transR.
    apply: ihm...
    apply: conv_sym... }
Qed.

Theorem sta_unicity Γ m s t :
  Γ ⊢ m : Sort s -> Γ ⊢ m : Sort t -> s = t.
Proof.
  move=>tym1 tym2.
  apply: sim_sort.
  apply: sta_uniq tym1 tym2 (sta_ctx_sim_reflexive _).
Qed.
