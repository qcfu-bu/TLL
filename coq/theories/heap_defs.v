From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
From deriving Require Export deriving.
From extructures Require Export ord fset fmap.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset_scope.
Declare Scope heap_scope.
Local Open Scope heap_scope.

Definition heap := {fmap nat -> term * sort}.

Definition hkey (H : heap) (s : sort) : Prop := 
  forall l, match H l, s with
       | Some (_, U), _ => true 
       | Some (_, L), U => false
       | Some (_, L), L => true
       | None, _ => true
       end.
Notation "H ▷ s" := (hkey H s) (at level 40) : heap_scope.

Definition hmrg (H1 H2 H3 : heap) : Prop :=
  forall l, match H1 l, H2 l, H3 l with
       | Some (m1, U), Some (m2, U), Some (m3, U) => m1 = m2 /\ m2 = m3
       | Some (m1, L), None, Some (m3, L) => m1 = m3
       | None, Some (m2, L), Some (m3, L) => m2 = m3
       | None, None, None => true
       | _, _, _ => false
       end.

Ltac rsplit := repeat split.
Ltac rmatch_case :=
  repeat match goal with
    | [ |- context[match ?x with _ => _ end] ] => case_eq x
    | [ |- context[let (_, _) := ?x in _] ] => destruct x
    | [ |- forall _, _ ] => intro
    end;
  intuition; subst=>//=.

Notation "H1 ∘ H2 => H" := (hmrg H1 H2 H) (at level 40) : heap_scope.

Lemma hdomm_bound (H : heap) : exists x, forall l, x < l -> l \notin domm H.
Proof.
  move e:(domm H)=>D {H e}. move: D. apply: fset_ind.
  exists 0=>l _. by rewrite in_fset0.
  move=>x D0 h0[x0 ih]. exists (maxn x x0)=> l h1.
  apply/negP=>h2. rewrite gtn_max in h1. move: h1=>/andP[h3 /ih h4]{ih}.
  move: h2. rewrite in_fsetU=>/orP[|h5].
  rewrite in_fset1=>/eqP e. subst. rewrite ltnn in h3. by move: h3=>/negP.
  rewrite h5 in h4. by move: h4=>/negP. 
Qed.

Lemma hdomm_exist (H : heap) : exists l, l \notin domm H.
Proof.
  have[x h]:=hdomm_bound H.
  have{}h:=h x.+1 (ltnSn _).
  by exists x.+1.
Qed.

Lemma remm_setm (H : heap) l v : l \notin domm H -> remm (setm H l v) l = H.
Proof.
  move=>h. apply eq_fmap=>x.
  rewrite remmE. case_eq (x == l)=>[/eqP e|e]; subst.
  by move: h=>/dommPn->.
  by rewrite setmE e.
Qed.

Lemma hkey_setm H m s l : H ▷ s -> setm H l (m, U) ▷ s.
Proof.
  move=>k l0.
  rewrite setmE. case_eq (l0 == l)=>//.
Qed.

Lemma hkey_remm H l s : H ▷ s -> remm H l ▷ s.
Proof.
  move=>k x.
  rewrite remmE.
  case_eq (x == l)=>//.
Qed.

Lemma hkey_unionm H1 H2 s :
  domm H1 :#: domm H2 -> H1 ▷ s -> H2 ▷ U -> unionm H1 H2 ▷ s.
Proof.
  move=>d k1 k2 l.
  rewrite unionmE.
  have:=k1 l. have:=k2 l.
  rmatch_case.
Qed.

Lemma hkey_impure H : H ▷ L.
Proof. move=>l. case (H l)=>//p. case p=>m[|]//. Qed.

Lemma hkey_merge H1 H2 H s : H1 ∘ H2 => H -> H1 ▷ s -> H2 ▷ s -> H ▷ s.
Proof.
  move=>mrg k1 k2 l.
  have:=k1 l. have:=k2 l. have:=mrg l.
  rmatch_case.
Qed.

Lemma hmrg_none H1 H2 H l :
  H1 ∘ H2 => H -> l \notin domm H -> l \notin domm H1 /\ l \notin domm H2.
Proof.
  move=>mrg/dommPn h1. split; apply/dommPn.
  move: (mrg l). rewrite h1. by rmatch_case.
  move: (mrg l). rewrite h1. by rmatch_case.
Qed.

Lemma hmrg_domm H1 H2 H l :
  H1 ∘ H2 => H -> l \in domm H1 -> l \in domm H.
Proof.
  move=>mrg/dommP[m e].
  apply/dommP.
  have:=mrg l. rewrite e.
  rmatch_case.
  by exists (t, U).
  by exists (t, L).
Qed.

Lemma hmrg_setmU H1 H2 H m l :
  H1 ∘ H2 => H -> setm H1 l (m, U) ∘ setm H2 l (m, U) => setm H l (m, U).
Proof.
  move=>mrg l0. rewrite!setmE. case_eq (l0 == l)=>//e.
  by have:=mrg l0.
Qed.

Lemma hmrg_setmL H1 H2 H m l :
  l \notin domm H -> H1 ∘ H2 => H -> setm H1 l (m, L) ∘ H2 => setm H l (m, L).
Proof.
  move=>h0 mrg l0. rewrite!setmE. case_eq (l0 == l)=>[/eqP e|e]; subst.
  by have[_/dommPn->]:=hmrg_none mrg h0.
  by have:=mrg l0.
Qed.

Lemma hmrg_unionm H0 H1 H2 H :
  H0 ▷ U -> domm H :#: domm H0 -> H1 ∘ H2 => H -> unionm H1 H0 ∘ unionm H2 H0 => unionm H H0.
Proof.
  move=>k d mrg l. rewrite!unionmE.
  case_eq (H1 l); case_eq (H2 l)=>//=.
  { have:=mrg l. rmatch_case.
    inv H19. by inv H22.
    inv H19. by inv H6. }
  { have:=mrg l. rmatch_case.
    { move: d=>/fdisjointP h.
      have h0:H l. by rewrite H12.
      rewrite-mem_domm in h0.
      have{h h0}/dommPn e:=h _ h0.
      rewrite e in H5. by inv H5. }
    { move: d=>/fdisjointP h.
      have h0:H l. by rewrite H8.
      rewrite-mem_domm in h0.
      have{h h0}/dommPn e:=h _ h0.
      rewrite e in H5. by inv H5. }
    { inv H19. by inv H7. } }
  { have:=mrg l. rmatch_case.
    { move: d=>/fdisjointP h.
      have h0:H l. by rewrite H12.
      rewrite-mem_domm in h0.
      have{h h0}/dommPn e:=h _ h0.
      rewrite e in H5. by inv H5. }
    { move: d=>/fdisjointP h.
      have h0:H l. by rewrite H8.
      rewrite-mem_domm in h0.
      have{h h0}/dommPn e:=h _ h0.
      rewrite e in H5. by inv H5. }
    { inv H18. by inv H7. } }
  { have:=mrg l. rmatch_case.
    have:=k l. by rewrite H6. }
Qed.

Lemma hmrg_pure_refl H : H ▷ U -> H ∘ H => H.
Proof.
  move=>k l.
  have:=k l.
  case_eq (H l)=>p. case: p=>m[|]//=.
  by [].
Qed.

Lemma hpure_split H :
  H ▷ U -> exists H1 H2, H1 ▷ U /\ H2 ▷ U /\ H1 ∘ H2 => H.
Proof.
  move=>k. exists H. exists H.
  repeat split=>//.
  exact: hmrg_pure_refl.
Qed.

Lemma hmrg_sym H1 H2 H : H1 ∘ H2 => H -> H2 ∘ H1 => H.
Proof.
  move=>mrg l.
  have:=mrg l.
  case_eq (H l); case_eq (H2 l); case_eq (H1 l)=>//.
  rmatch_case.
  { move=>p1 e1 p2 e2 e.
    case: p2 e2; case: p1 e1=>m1[|]e1 m2[|]e2//. }
Qed.

Lemma hmrg_pure H1 H2 H : H1 ∘ H2 => H -> H1 ▷ U -> H2 ▷ U -> H ▷ U.
Proof. exact: hkey_merge. Qed.

Lemma hmrg_pureL H1 H2 H : H1 ∘ H2 => H -> H1 ▷ U -> H = H2.
Proof.
  move=>mrg k. apply eq_fmap.
  move=>l.
  have:=mrg l. have:=k l.
  case_eq (H l); case_eq (H2 l); case_eq (H1 l)=>//.
  rmatch_case.
  { move=>e1 p2 e2 p e.
    case: p e; case: p2 e2=>m2[|]e2 m0[|]e0=>//.
    by move=>_->. }
  { move=>p1 e1 e2 p e.
    by case: p e; case: p1 e1=>m1[|]e1 m0[|]e0=>//. }
  { move=>p1 e1 p2 e2 e.
    by case: p2 e2; case: p1 e1=>m2[|]e2 m1[|]e1=>//. }
  { move=>e1 p2 e2 e _.
    by case: p2 e2=>m2[|]e2//. }
Qed.

Lemma hmrg_pureR H1 H2 H : H1 ∘ H2 => H -> H2 ▷ U -> H = H1.
Proof.    
  move=>mrg k.
  apply: hmrg_pureL.
  apply: hmrg_sym.
  exact: mrg.
  exact: k.
Qed.

Lemma hmrg_splitL H1 H2 H Ha Hb :
  H1 ∘ H2 => H -> Ha ∘ Hb => H1 -> exists Hc, Ha ∘ H2 => Hc /\ Hc ∘ Hb => H.
Proof.
  move=>mrg1 mrg2. exists (unionm Ha H2). split.
  { move=>l.
    have:=mrg1 l. have:=mrg2 l. rmatch_case.
    all: repeat match goal with
           | [ H1 : context[unionm ?H _], H2 : context[?H] |- _ ] => 
               rewrite unionmE H2 in H1; simpl in H1; inv H1; eauto
           end.
    all: repeat match goal with
           | [ H1 : ?H = _, H2 : ?H = _ |- _ ] =>
               rewrite H1 in H2; inv H2; eauto
           end. }
  { move=>l.
    have:=mrg1 l. have:=mrg2 l. rmatch_case.
    all: repeat match goal with
           | [ H1 : context[unionm ?H _], H2 : context[?H] |- _ ] => 
               rewrite unionmE H2 in H1; simpl in H1; inv H1; eauto
           end.
    all: repeat match goal with
           | [ H1 : ?H = _, H2 : ?H = _ |- _ ] =>
               rewrite H1 in H2; inv H2; eauto
           end. }
Qed.

Lemma hmrg_splitR H1 H2 H Ha Hb :
  H1 ∘ H2 => H -> Ha ∘ Hb => H1 -> exists Hc, Hb ∘ H2 => Hc /\ Hc ∘ Ha => H.
Proof.
  move=>mrg1 mrg2.
  apply: hmrg_splitL.
  exact: mrg1.
  exact: hmrg_sym.
Qed.

Lemma hmrg_distr H1 H2 H H11 H12 H21 H22 :
  H1 ∘ H2 => H ->
  H11 ∘ H12 => H1 ->
  H21 ∘ H22 => H2 ->
  exists H1' H2',
    H1' ∘ H2' => H /\
    H11 ∘ H21 => H1' /\
    H12 ∘ H22 => H2'.
Proof.
  move=>mrg0 mrg1 mrg2.
  have[H3[mrg3 mrg4]]:=hmrg_splitL mrg0 mrg1.
  have[H4[mrg5 mrg6]]:=hmrg_splitL (hmrg_sym mrg3) mrg2.
  have[H5[mrg7 mrg8]]:=hmrg_splitR mrg4 mrg6.
  exists H4. exists H5. repeat split.
  exact: (hmrg_sym mrg8).
  exact: (hmrg_sym mrg5).
  exact: (hmrg_sym mrg7).
Qed.

Lemma hsplit_self H : exists H', H' ▷ U /\ H ∘ H' => H.
Proof.
  exists (filterm (fun _ (p : term * sort) =>
                let (_, s) := p in
                match s with
                | U => true
                | L => false
                end) H).
  split.
  { move=>l.
    rewrite filtermE.
    case_eq (H l)=>//=p.
    by case: p=>m[|]. }
  { move=>l. rewrite filtermE.
    case_eq (H l)=>//=p.
    by case: p=>m[|]. }
Qed.
