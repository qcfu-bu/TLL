From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_uniq eproc_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma proc_eproc_type Θ p : Θ ⊢ p -> exists p', Θ ⊢ p ~ p'. 
Proof with eauto using eproc_type.
  elim=>{Θ p}.
  { move=>Θ m tym.
    have[m' erm]:=dyn_era_type tym. exists ⟨ m' ⟩... }
  { move=>Θ1 Θ2 Θ p q mrg typ[p' erp]tyq[q' erq]. exists (p' ∣ q')... }
  { move=>Θ p r1 r2 A e typ[p' erp]. exists (ν.p')... }
Qed.

Fixpoint erasep (p : proc) : proc :=
  match p with
  | Exp m => Exp (erase m)
  | Par p q => Par (erasep p) (erasep q)
  | Nu p => Nu (erasep p)
  end.

Lemma eproc_type_erasep Θ p p' :
  Θ ⊢ p ~ p' -> p' = erasep p.
Proof with eauto.
  elim=>//={Θ p p'}.
  { move=>Θ m m' erm. by have->:=era_type_erase erm. }
  { move=>Θ1 Θ2 Θ p p' q q' mrg erp->erq->. by []. }
  { move=>Θ p p' r1 r2 A xor erp->. by []. }
Qed.

Lemma eproc_unicity Θ p p1 p2 :
  Θ ⊢ p ~ p1 -> Θ ⊢ p ~ p2 -> p1 = p2.
Proof with eauto.
  move=>er1 er2.
  have->:=eproc_type_erasep er1.
  have->:=eproc_type_erasep er2.
  by [].
Qed.
    
