From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
From deriving Require Import deriving.
From extructures Require Export ord fset fmap.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Heap.

Declare Scope heap_scope.
Open Scope heap_scope.

Definition heap := {fmap nat -> term * sort}.

Definition hkey (H : heap) (s : sort) : Prop := 
  forall l, match H l, s with
       | Some (_, U), _ => true 
       | Some (_, L), U => false
       | Some (_, L), L => true
       | None, _ => true
       end.
Notation "H ▷ s" := (hkey H s) (at level 40).

Definition hmrg (H1 H2 H3 : heap) : Prop :=
  forall l, match H1 l, H2 l, H3 l with
       | Some (m1, U), Some (m2, U), Some (m3, U) => m1 = m2 /\ m2 = m3
       | Some (m1, L), None, Some (m3, L) => m1 = m3
       | None, Some (m2, L), Some (m3, L) => m2 = m3
       | None, None, None => True
       | _, _, _ => False
       end.
Notation "H1 ∘ H2 => H" := (hmrg H1 H2 H) (at level 40).

Lemma hkey_impure H : H ▷ L.
Proof. move=>l. case (H l)=>//p. case p=>m[|]//. Qed.

Lemma hkey_merge H1 H2 H s : H1 ∘ H2 => H -> H1 ▷ s -> H2 ▷ s -> H ▷ s.
Proof.
  move=>mrg k1 k2 l.
  have:=k1 l. have:=k2 l. have:=mrg l.
  case_eq (H l); case_eq (H2 l); case_eq (H1 l)=>//.
  { move=>p1 e1 p2 e2 p e.
    by case: p e; case: p2 e2; case: p1 e1=>m1[|]e1 m2[|]e2 m0[|]e0=>//. }
  { move=>e1 p2 e2 p e.
    by case: p e; case: p2 e2=>m2[|]e2 m0[|]e0=>//. }
  { move=>p1 e1 p2 p e.
    by case: p e; case: p1 e1=>m1[|]e1 m0[|]e0=>//. }
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
  { move=>p1 e1 p2 e2 p e.
    case: p e; case: p2 e2; case: p1 e1=>m1[|]e1 m2[|]e2 m0[|]e0//.
    by move=>[->->]. }
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
  { move=>p1 e1 p2 e2 p e.
    case: p e; case: p2 e2; case: p1 e1=>m1[|]e1 m2[|]e2 m0[|]e0//.
    by move=>_[<-->]. }
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
    have:=mrg1 l. have:=mrg2 l.
    (repeat match goal with
       | [ |- context[match ?x with _ => _ end] ] =>
           case_eq x
       | [ |- context[let (_, _) := ?x in _] ] => destruct x
       | [ |- forall _, _ ] => intro
       end; subst);
    intuition; subst=>//.
    all: repeat match goal with
           | [ H1 : context[unionm ?H _], H2 : context[?H] |- _ ] => 
               rewrite unionmE H2 in H1; simpl in H1; inv H1; eauto
           end.
    all: repeat match goal with
           | [ H1 : ?H = _, H2 : ?H = _ |- _ ] =>
               rewrite H1 in H2; inv H2; eauto
           end. }
  { move=>l.
    have:=mrg1 l. have:=mrg2 l.
    (repeat match goal with
       | [ |- context[match ?x with _ => _ end] ] =>
           case_eq x
       | [ |- context[let (_, _) := ?x in _] ] => destruct x
       | [ |- forall _, _ ] => intro
       end; subst);
    intuition; subst=>//.
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
  
End Heap.
