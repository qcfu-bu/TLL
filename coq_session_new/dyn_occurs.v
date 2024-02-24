From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_conf sta_uniq dyn_type dyn_cren dyn_valid dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive cvar_pos : dyn_ctx -> cvar -> bool -> Prop :=
| cvar_pos_nil i :
  cvar_pos nil i false
| cvar_pos_ty Θ A :
  cvar_pos (A :L Θ) 0 true
| cvar_pos_n Θ :
  cvar_pos (_: Θ) 0 false
| cvar_pos_cons Θ x A b :
  cvar_pos Θ x b ->
  cvar_pos (A :: Θ) x.+1 b.

Fixpoint dyn_occurs (i : cvar) (m : term) : nat :=
  match m with
  | Var _ => 0
  | Sort _ => 0
  | Pi0 _ _ _ => 0
  | Pi1 _ _ _ => 0
  | Lam0 _ m _ => dyn_occurs i m
  | Lam1 _ m _ => dyn_occurs i m
  | App0 m _ => dyn_occurs i m
  | App1 m n => dyn_occurs i m + dyn_occurs i n
  | Sig0 _ _ _ => 0
  | Sig1 _ _ _ => 0
  | Pair0 _ n _ => dyn_occurs i n
  | Pair1 m n _ => dyn_occurs i m + dyn_occurs i n
  | LetIn _ m n => dyn_occurs i m + dyn_occurs i n
  | Fix _ m => dyn_occurs i m
  | Unit => 0
  | Bool => 0
  | II => 0
  | TT => 0
  | FF => 0
  | Ifte _ m n1 n2  => dyn_occurs i m + maxn (dyn_occurs i n1) (dyn_occurs i n2)
  | IO _ => 0
  | Return m => dyn_occurs i m
  | Bind m n => dyn_occurs i m + dyn_occurs i n
  | Proto => 0
  | Stop => 0
  | Act0 _ _ _ => 0
  | Act1 _ _ _ => 0
  | Ch _ _ => 0
  | CVar x => if x == i then 1 else 0
  | Fork _ m => dyn_occurs i m
  | Recv0 m => dyn_occurs i m
  | Recv1 m => dyn_occurs i m
  | Send0 m => dyn_occurs i m
  | Send1 m => dyn_occurs i m
  | Close m => dyn_occurs i m
  | Wait m => dyn_occurs i m
  | Box => 0
  end.

Lemma cvar_pos_merge_false Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> 
  cvar_pos Θ1 i false ->
  cvar_pos Θ2 i false ->
  cvar_pos Θ i false.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1. inv pos2... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1. inv pos2... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1; inv pos2... }
  { move=>Θ1 Θ2 Θ mrg ih i pos1 pos2. inv pos1; inv pos2... }
Qed.

Lemma cvar_pos_split_false Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ i false ->
  cvar_pos Θ1 i false /\
  cvar_pos Θ2 i false.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ mrg ih i pos. inv pos...
    have[pos1 pos2]:=ih _ H3... }
Qed.

Lemma cvar_pos_split_true Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ i true ->
  (cvar_pos Θ1 i false /\ cvar_pos Θ2 i true) \/
  (cvar_pos Θ1 i true /\ cvar_pos Θ2 i false).
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}.
  { move=>i pos. inv pos. }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    right...
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    left...
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ mrg ih i pos. inv pos.
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
Qed.

Lemma dyn_empty_pos_true Θ i : dyn_empty Θ -> cvar_pos Θ i true -> False.
Proof.
  move=>emp. elim: emp i=>{Θ}.
  { move=>i pos. inv pos. }
  { move=>Δ emp ih i pos. inv pos.
    apply: ih. apply: H3. }
Qed.

Lemma dyn_empty_pos_false Θ i : dyn_empty Θ -> cvar_pos Θ i false.
Proof.
  move=>emp. elim: emp i=>{Θ}.
  { move=>i. constructor. }
  { move=>Δ emp ih[|i].
    constructor.
    by constructor. }
Qed.

Lemma dyn_just_pos_true Θ x i A :
  dyn_just Θ x A -> cvar_pos Θ i true <-> x == i = true.
Proof with eauto.
  move=>js. elim: js i=>{Θ x A}.
  { move=>Δ A emp i. split.
    { move=>pos. inv pos=>//.
      exfalso. apply: dyn_empty_pos_true... }
    { move=>/eqP<-. constructor. } }
  { move=>Δ A x js ih i. split.
    { move=>pos. inv pos. move/ih in H3... }
    { move=>/eqP<-. constructor.
      rewrite ih. by apply/eqP. } }
Qed.

Lemma dyn_just_pos_false Θ x i A :
  dyn_just Θ x A -> cvar_pos Θ i false <-> x == i = false.
Proof with eauto.
  move=>js. elim: js i=>{Θ x A}.
  { move=>Δ A emp i. split.
    { move=>pos. inv pos. by apply/eqP. }
    { move: i=>[|i]/eqP//_.
      constructor. by apply: dyn_empty_pos_false. } }
  { move=>Δ A x js ih i. split. 
    { move=>pos. inv pos.
      by apply/eqP.
      move/ih in H3... }
    { move: i=>[|i] neq...
      constructor.
      constructor.
      rewrite ih... } }
Qed.

Lemma dyn_type_occurs0 Θ Γ Δ m A i :
  Θ ; Γ ; Δ ⊢ m : A -> cvar_pos Θ i false -> dyn_occurs i m = 0.
Proof with eauto using dyn_occurs.
  move=>ty. elim: ty i=>//={Θ Γ Δ m A}...
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
            tyA tym ihm tyn1 ihn1 tyn2 ihn2 i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->:=ihn1 _ pos2.
    have->//:=ihn2 _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ Γ Δ r x A js wf k tyA i pos.
    move/(dyn_just_pos_false _ js) in pos.
    rewrite pos... }
Qed.

Lemma dyn_type_occurs1 Θ Γ Δ m A i :
  Θ ; Γ ; Δ ⊢ m : A -> cvar_pos Θ i true -> dyn_occurs i m = 1.
Proof with eauto using dyn_occurs, dyn_type_occurs0.
  move=>ty. elim: ty i=>//={Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { rewrite ihm... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
            tyS tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
            tyC tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
            tyC tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn1...
      erewrite ihn2...
      erewrite dyn_type_occurs0... }
    { erewrite ihm...
      erewrite dyn_type_occurs0...
      erewrite dyn_type_occurs0... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ Γ Δ r x A js wf k tyA i pos.
    move/(dyn_just_pos_true _ js) in pos.
    rewrite pos... }
Qed.

Definition iren i (ξ : cvar -> cvar) := forall x, ξ x == i = false.

Lemma iren0 : iren 0 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren1 : iren 1 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren_upren i ξ : iren i ξ -> iren i.+1 (upren ξ).
Proof.
  move=> ir x.
  elim: x.
  asimpl; eauto.
  asimpl=>n e; eauto.
Qed.

Lemma dyn_occurs_iren Θ Γ Δ m A i ξ :
  Θ ; Γ ; Δ ⊢ cren ξ m : A -> iren i ξ -> dyn_occurs i (cren ξ m) = 0.
Proof with eauto using dyn_occurs.
  move e:(cren ξ m)=>x ty.
  elim: ty m ξ e i=>//={Θ Γ Δ x A}...
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
           tyS tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 m0 ξ e i h.
    destruct m0; inv e.
    erewrite ihm... erewrite ihn1... erewrite ihn2... }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ Γ Δ r x A js wf k tyA m ξ e i h.
    destruct m; inv e.
    by rewrite h. }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ m tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ m tym ihm m0 ξ e i h.
    destruct m0; inv e... }
Qed.
