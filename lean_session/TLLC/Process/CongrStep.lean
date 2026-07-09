import TLLC.Process.Congr
import TLLC.Dynamic.Inversion

/-!
# Structural term congruence versus dynamic reduction

`CongrTerm .ex` equates terms up to their erased implicit positions. This file proves the
commutation facts the reflection theorem needs at the term level:

* `CongrTerm.to_im`: any congruence weakens to the implicit level;
* `CongrTerm.trans`: congruence is transitive;
* `Typed.occursEx_zero`: a variable with a `none` linear slot has no explicit occurrence
  (implicitly bound variables are used only inside erased positions);
* `congrTerm_tsubst_of_occursEx`: term substitutions with implicitly-related images produce
  congruent instances, provided explicitly occurring variables get explicitly-related images;
* `congrTerm_step_reflect`: a step of the congruent copy of a *well-typed* term reflects to a step
  of the term itself, with congruent results. Typing is essential: the implicit β/projection rules
  substitute payloads that are only implicitly related, which is sound exactly because typed bodies
  use implicitly-bound variables only in erased positions.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-! ## Explicit occurrences of term variables -/

/-- The number of occurrences of term variable `i` at explicit positions, mirroring the subterm
discipline of dynamic typing (and of `Dynamic.occurs` for channels), with de Bruijn lifting at
term binders. -/
def occursEx (i : Nat) : Term → Nat
  | .var_Term x => if x = i then 1 else 0
  | .srt _ => 0
  | .pi _ _ _ _ => 0
  | .lam _ m _ _ => occursEx (i + 1) m
  | .app m _ .im => occursEx i m
  | .app m n .ex => occursEx i m + occursEx i n
  | .sig _ _ _ _ => 0
  | .pair _ n .im _ => occursEx i n
  | .pair m n .ex _ => occursEx i m + occursEx i n
  | .proj _ m n => occursEx i m + occursEx (i + 2) n
  | .fix _ m => occursEx (i + 1) m
  | .unit => 0
  | .one => 0
  | .bool => 0
  | .tt => 0
  | .ff => 0
  | .ite _ m n1 n2 => occursEx i m + max (occursEx i n1) (occursEx i n2)
  | .M _ => 0
  | .pure m => occursEx i m
  | .mlet m n => occursEx i m + occursEx (i + 1) n
  | .proto => 0
  | .stop => 0
  | .act _ _ _ _ => 0
  | .ch _ _ => 0
  | .chan _ => 0
  | .fork _ m => occursEx (i + 1) m
  | .recv m _ => occursEx i m
  | .send m _ => occursEx i m
  | .close _ m => occursEx i m
  | .box => 0

/-- A `none` linear slot at de Bruijn index `i`. -/
inductive NPos : Ctx → Nat → Prop where
  | zero {Δ} :
    NPos (none :: Δ) 0
  | succ {Δ o x} :
    NPos Δ x →
    NPos (o :: Δ) (x + 1)

lemma _root_.TLLC.Dynamic.Has.ne_npos {Δ x s A} (has : Has Δ x s A) :
    ∀ i, NPos Δ i → x ≠ i := by
  induction has with
  | zero _ =>
      intro i np
      cases np with
      | succ _ => omega
  | succ _ ih =>
      intro i np
      cases np with
      | succ np' =>
          have := ih _ np'
          omega
  | null _ ih =>
      intro i np
      cases np with
      | zero => omega
      | succ np' =>
          have := ih _ np'
          omega

lemma _root_.TLLC.Dynamic.Merge.npos {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) :
    ∀ i, NPos Δ i → NPos Δ1 i ∧ NPos Δ2 i := by
  induction mrg with
  | nil => intro i np; cases np
  | left m _ ih =>
      intro i np
      cases np with
      | succ np' =>
          obtain ⟨h1, h2⟩ := ih _ np'
          exact ⟨NPos.succ h1, NPos.succ h2⟩
  | right1 m _ ih =>
      intro i np
      cases np with
      | succ np' =>
          obtain ⟨h1, h2⟩ := ih _ np'
          exact ⟨NPos.succ h1, NPos.succ h2⟩
  | right2 m _ ih =>
      intro i np
      cases np with
      | succ np' =>
          obtain ⟨h1, h2⟩ := ih _ np'
          exact ⟨NPos.succ h1, NPos.succ h2⟩
  | null _ ih =>
      intro i np
      cases np with
      | zero => exact ⟨NPos.zero, NPos.zero⟩
      | succ np' =>
          obtain ⟨h1, h2⟩ := ih _ np'
          exact ⟨NPos.succ h1, NPos.succ h2⟩

/-- Implicitly bound variables (with `none` linear slots) have no explicit occurrences in typed
terms: the dynamic `var` rule demands a live slot. -/
lemma _root_.TLLC.Dynamic.Typed.occursEx_zero {Θ Γ Δ m A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    ∀ i, NPos Δ i → occursEx i m = 0 := by
  induction ty with
  | var _ _ _ has =>
      intro i np
      simp only [occursEx]
      rw [if_neg (has.ne_npos i np)]
  | lamIm _ _ _ ih =>
      intro i np
      exact ih (i + 1) (NPos.succ np)
  | lamEx _ _ _ ih =>
      intro i np
      exact ih (i + 1) (NPos.succ np)
  | appIm _ _ ih =>
      intro i np
      exact ih i np
  | appEx _ mrgΔ _ _ ihm ihn =>
      intro i np
      obtain ⟨np1, np2⟩ := mrgΔ.npos i np
      simp only [occursEx]
      rw [ihm i np1, ihn i np2]
  | pairIm _ _ _ ih =>
      intro i np
      exact ih i np
  | pairEx _ mrgΔ _ _ _ ihm ihn =>
      intro i np
      obtain ⟨np1, np2⟩ := mrgΔ.npos i np
      simp only [occursEx]
      rw [ihm i np1, ihn i np2]
  | projIm _ mrgΔ _ _ _ ihm ihn =>
      intro i np
      obtain ⟨np1, np2⟩ := mrgΔ.npos i np
      simp only [occursEx]
      rw [ihm i np1, ihn (i + 2) (NPos.succ (NPos.succ np2))]
  | projEx _ mrgΔ _ _ _ ihm ihn =>
      intro i np
      obtain ⟨np1, np2⟩ := mrgΔ.npos i np
      simp only [occursEx]
      rw [ihm i np1, ihn (i + 2) (NPos.succ (NPos.succ np2))]
  | one => intro i np; rfl
  | tt => intro i np; rfl
  | ff => intro i np; rfl
  | ite _ mrgΔ _ _ _ _ ihm ihn1 ihn2 =>
      intro i np
      obtain ⟨np1, np2⟩ := mrgΔ.npos i np
      simp only [occursEx]
      rw [ihm i np1, ihn1 i np2, ihn2 i np2]
      rfl
  | pure _ ih =>
      intro i np
      exact ih i np
  | mlet _ mrgΔ _ _ _ ihm ihn =>
      intro i np
      obtain ⟨np1, np2⟩ := mrgΔ.npos i np
      simp only [occursEx]
      rw [ihm i np1, ihn (i + 1) (NPos.succ np2)]
  | chan _ _ _ _ => intro i np; rfl
  | fork _ ih =>
      intro i np
      exact ih (i + 1) (NPos.succ np)
  | recv _ _ ih =>
      intro i np
      exact ih i np
  | send _ _ ih =>
      intro i np
      exact ih i np
  | close _ ih =>
      intro i np
      exact ih i np
  | conv _ _ _ ih =>
      intro i np
      exact ih i np

/-! ## Congruence weakening, renaming stability, transitivity -/

/-- Every congruence weakens to the implicit level. -/
lemma CongrTerm.to_im {r : Rlv} {m n : Term} (e : CongrTerm r m n) :
    CongrTerm .im m n := by
  induction e with
  | var => exact .var
  | srt => exact .srt
  | pi eA eB _ _ => exact .pi eA eB
  | lam eA _ _ ihm => exact .lam eA ihm
  | app _ _ ihm ihn => exact .app ihm ihn
  | sig eA eB _ _ => exact .sig eA eB
  | pair _ _ ihm ihn => exact .pair ihm ihn
  | proj eC _ _ _ ihm ihn => exact .proj eC ihm ihn
  | fix eA _ _ ihm => exact .fix eA ihm
  | unit => exact .unit
  | one => exact .one
  | bool => exact .bool
  | tt => exact .tt
  | ff => exact .ff
  | ite eA _ _ _ _ ihm ihn1 ihn2 => exact .ite eA ihm ihn1 ihn2
  | M eA _ => exact .M eA
  | pure _ ihm => exact .pure ihm
  | mlet _ _ ihm ihn => exact .mlet ihm ihn
  | proto => exact .proto
  | stop => exact .stop
  | act eA eB _ _ => exact .act eA eB
  | ch eA _ => exact .ch eA
  | chan_im => exact .chan_im
  | chan_ex => exact .chan_im
  | fork eA _ _ ihm => exact .fork eA ihm
  | recv _ ihm => exact .recv ihm
  | send _ ihm => exact .send ihm
  | close _ ihm => exact .close ihm
  | box => exact .box

/-- Congruence is stable under term renaming. -/
lemma CongrTerm.trename {r : Rlv} {m m' : Term} (e : CongrTerm r m m') :
    ∀ ζ : Nat → Nat,
      CongrTerm r (m⟨(id : Nat → Nat); ζ⟩) (m'⟨(id : Nat → Nat); ζ⟩) := by
  induction e with
  | var =>
      intro ζ
      asimp
      exact CongrTerm.var
  | srt =>
      intro ζ
      asimp
      exact CongrTerm.srt
  | pi eA eB ihA ihB =>
      intro ζ
      asimp
      have hB := ihB (upRen_Term_Term ζ)
      asimp at hB
      exact CongrTerm.pi (ihA ζ) hB
  | lam eA em ihA ihm =>
      intro ζ
      asimp
      have hm := ihm (upRen_Term_Term ζ)
      asimp at hm
      exact CongrTerm.lam (ihA ζ) hm
  | app em en ihm ihn =>
      intro ζ
      asimp
      exact CongrTerm.app (ihm ζ) (ihn ζ)
  | sig eA eB ihA ihB =>
      intro ζ
      asimp
      have hB := ihB (upRen_Term_Term ζ)
      asimp at hB
      exact CongrTerm.sig (ihA ζ) hB
  | pair em en ihm ihn =>
      intro ζ
      asimp
      exact CongrTerm.pair (ihm ζ) (ihn ζ)
  | proj eC em en ihC ihm ihn =>
      intro ζ
      asimp
      have hC := ihC (upRen_Term_Term ζ)
      have hn := ihn (upRen_Term_Term (upRen_Term_Term ζ))
      asimp at hC hn
      exact CongrTerm.proj hC (ihm ζ) hn
  | fix eA em ihA ihm =>
      intro ζ
      asimp
      have hm := ihm (upRen_Term_Term ζ)
      asimp at hm
      exact CongrTerm.fix (ihA ζ) hm
  | unit =>
      intro ζ
      asimp
      exact CongrTerm.unit
  | one =>
      intro ζ
      asimp
      exact CongrTerm.one
  | bool =>
      intro ζ
      asimp
      exact CongrTerm.bool
  | tt =>
      intro ζ
      asimp
      exact CongrTerm.tt
  | ff =>
      intro ζ
      asimp
      exact CongrTerm.ff
  | ite eA em en1 en2 ihA ihm ihn1 ihn2 =>
      intro ζ
      asimp
      have hA := ihA (upRen_Term_Term ζ)
      asimp at hA
      exact CongrTerm.ite hA (ihm ζ) (ihn1 ζ) (ihn2 ζ)
  | M eA ihA =>
      intro ζ
      asimp
      exact CongrTerm.M (ihA ζ)
  | pure em ihm =>
      intro ζ
      asimp
      exact CongrTerm.pure (ihm ζ)
  | mlet em en ihm ihn =>
      intro ζ
      asimp
      have hn := ihn (upRen_Term_Term ζ)
      asimp at hn
      exact CongrTerm.mlet (ihm ζ) hn
  | proto =>
      intro ζ
      asimp
      exact CongrTerm.proto
  | stop =>
      intro ζ
      asimp
      exact CongrTerm.stop
  | act eA eB ihA ihB =>
      intro ζ
      asimp
      have hB := ihB (upRen_Term_Term ζ)
      asimp at hB
      exact CongrTerm.act (ihA ζ) hB
  | ch eA ihA =>
      intro ζ
      asimp
      exact CongrTerm.ch (ihA ζ)
  | chan_im =>
      intro ζ
      asimp
      exact CongrTerm.chan_im
  | chan_ex =>
      intro ζ
      asimp
      exact CongrTerm.chan_ex
  | fork eA em ihA ihm =>
      intro ζ
      asimp
      have hm := ihm (upRen_Term_Term ζ)
      asimp at hm
      exact CongrTerm.fork (ihA ζ) hm
  | recv em ihm =>
      intro ζ
      asimp
      exact CongrTerm.recv (ihm ζ)
  | send em ihm =>
      intro ζ
      asimp
      exact CongrTerm.send (ihm ζ)
  | close em ihm =>
      intro ζ
      asimp
      exact CongrTerm.close (ihm ζ)
  | box =>
      intro ζ
      asimp
      exact CongrTerm.box

/-- Congruence is transitive. -/
lemma CongrTerm.trans {r : Rlv} {m1 m2 : Term} (e1 : CongrTerm r m1 m2) :
    ∀ {m3 : Term}, CongrTerm r m2 m3 → CongrTerm r m1 m3 := by
  induction e1 with
  | var => intro m3 e2; exact e2
  | srt => intro m3 e2; exact e2
  | pi _ _ ihA ihB =>
      intro m3 e2
      cases e2 with
      | pi eA' eB' => exact .pi (ihA eA') (ihB eB')
  | lam _ _ ihA ihm =>
      intro m3 e2
      cases e2 with
      | lam eA' em' => exact .lam (ihA eA') (ihm em')
  | app _ _ ihm ihn =>
      intro m3 e2
      cases e2 with
      | app em' en' => exact .app (ihm em') (ihn en')
  | sig _ _ ihA ihB =>
      intro m3 e2
      cases e2 with
      | sig eA' eB' => exact .sig (ihA eA') (ihB eB')
  | pair _ _ ihm ihn =>
      intro m3 e2
      cases e2 with
      | pair em' en' => exact .pair (ihm em') (ihn en')
  | proj _ _ _ ihC ihm ihn =>
      intro m3 e2
      cases e2 with
      | proj eC' em' en' => exact .proj (ihC eC') (ihm em') (ihn en')
  | fix _ _ ihA ihm =>
      intro m3 e2
      cases e2 with
      | fix eA' em' => exact .fix (ihA eA') (ihm em')
  | unit => intro m3 e2; exact e2
  | one => intro m3 e2; exact e2
  | bool => intro m3 e2; exact e2
  | tt => intro m3 e2; exact e2
  | ff => intro m3 e2; exact e2
  | ite _ _ _ _ ihA ihm ihn1 ihn2 =>
      intro m3 e2
      cases e2 with
      | ite eA' em' en1' en2' =>
          exact .ite (ihA eA') (ihm em') (ihn1 en1') (ihn2 en2')
  | M _ ihA =>
      intro m3 e2
      cases e2 with
      | M eA' => exact .M (ihA eA')
  | pure _ ihm =>
      intro m3 e2
      cases e2 with
      | pure em' => exact .pure (ihm em')
  | mlet _ _ ihm ihn =>
      intro m3 e2
      cases e2 with
      | mlet em' en' => exact .mlet (ihm em') (ihn en')
  | proto => intro m3 e2; exact e2
  | stop => intro m3 e2; exact e2
  | act _ _ ihA ihB =>
      intro m3 e2
      cases e2 with
      | act eA' eB' => exact .act (ihA eA') (ihB eB')
  | ch _ ihA =>
      intro m3 e2
      cases e2 with
      | ch eA' => exact .ch (ihA eA')
  | chan_im =>
      intro m3 e2
      cases e2 with
      | chan_im => exact .chan_im
  | chan_ex =>
      intro m3 e2
      cases e2 with
      | chan_ex => exact .chan_ex
  | fork _ _ ihA ihm =>
      intro m3 e2
      cases e2 with
      | fork eA' em' => exact .fork (ihA eA') (ihm em')
  | recv _ ihm =>
      intro m3 e2
      cases e2 with
      | recv em' => exact .recv (ihm em')
  | send _ ihm =>
      intro m3 e2
      cases e2 with
      | send em' => exact .send (ihm em')
  | close _ ihm =>
      intro m3 e2
      cases e2 with
      | close em' => exact .close (ihm em')
  | box => intro m3 e2; exact e2

/-! ## Substitution congruence -/

private lemma congr_up_im {τ τ' : Nat → Term}
    (h : ∀ x, CongrTerm .im (τ x) (τ' x)) :
    ∀ x, CongrTerm .im (up_Term_Term τ x) (up_Term_Term τ' x) := by
  intro x
  cases x with
  | zero =>
      asimp
      exact CongrTerm.var
  | succ x =>
      have hx := (h x).trename (· + 1)
      asimp at hx ⊢
      exact hx

/-- Substituting implicitly-related payloads produces congruent terms, provided every explicitly
occurring variable receives explicitly-related payloads. -/
lemma congrTerm_tsubst_of_occursEx {r : Rlv} {b b' : Term} (e : CongrTerm r b b') :
    ∀ (τ τ' : Nat → Term),
      (∀ x, CongrTerm .im (τ x) (τ' x)) →
      (r = .ex → ∀ x, occursEx x b ≠ 0 → CongrTerm .ex (τ x) (τ' x)) →
      CongrTerm r (b[Chan.var_Chan; τ]) (b'[Chan.var_Chan; τ']) := by
  induction e with
  | @var x r =>
      intro τ τ' him hex
      asimp
      cases r with
      | im => exact him x
      | ex =>
          refine hex rfl x ?_
          simp [occursEx]
  | srt =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.srt
  | pi eA eB ihA ihB =>
      intro τ τ' him hex
      asimp
      have hA := ihA τ τ' him (fun hr => nomatch hr)
      have hB := ihB (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr => nomatch hr)
      asimp at hB
      exact CongrTerm.pi hA hB
  | @lam A A' m m' r1 r2 s _ _ ihA ihm =>
      intro τ τ' him hex
      asimp
      have hA := ihA τ τ' him (fun hr => nomatch hr)
      have hm := ihm (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr x hx => by
          cases x with
          | zero => asimp; exact CongrTerm.var
          | succ x =>
              have h := (hex hr x (by simp only [occursEx]; omega)).trename (· + 1)
              asimp at h ⊢
              exact h)
      asimp at hm
      exact CongrTerm.lam hA hm
  | @app m m' n n' r1 r2 _ _ ihm ihn =>
      intro τ τ' him hex
      asimp
      refine CongrTerm.app
        (ihm τ τ' him (fun hr x hx => hex hr x (by
          subst hr
          cases r2 <;> simp only [occursEx] <;> omega))) ?_
      cases r2 with
      | im =>
          cases r1 <;> exact (ihn τ τ' him (fun hr => nomatch hr)).to_im
      | ex =>
          refine ihn τ τ' him (fun hr x hx => ?_)
          cases r1 with
          | im => cases hr
          | ex => exact hex rfl x (by simp only [occursEx]; omega)
  | sig eA eB ihA ihB =>
      intro τ τ' him hex
      asimp
      have hA := ihA τ τ' him (fun hr => nomatch hr)
      have hB := ihB (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr => nomatch hr)
      asimp at hB
      exact CongrTerm.sig hA hB
  | @pair m m' n n' r1 r2 s _ _ ihm ihn =>
      intro τ τ' him hex
      asimp
      refine CongrTerm.pair ?_
        (ihn τ τ' him (fun hr x hx => hex hr x (by
          subst hr
          cases r2 <;> simp only [occursEx] <;> omega)))
      cases r2 with
      | im =>
          cases r1 <;> exact (ihm τ τ' him (fun hr => nomatch hr)).to_im
      | ex =>
          refine ihm τ τ' him (fun hr x hx => ?_)
          cases r1 with
          | im => cases hr
          | ex => exact hex rfl x (by simp only [occursEx]; omega)
  | proj eC em en ihC ihm ihn =>
      intro τ τ' him hex
      asimp
      have hC := ihC (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr => nomatch hr)
      have hm := ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega))
      have hn := ihn (up_Term_Term (up_Term_Term τ)) (up_Term_Term (up_Term_Term τ'))
        (congr_up_im (congr_up_im him))
        (fun hr x hx => by
          cases x with
          | zero => asimp; exact CongrTerm.var
          | succ x =>
              cases x with
              | zero => asimp; exact CongrTerm.var
              | succ x =>
                  have h := ((hex hr x (by
                    simp only [occursEx]
                    rw [show x + 1 + 1 = x + 2 from by omega] at hx
                    omega)).trename (· + 1)).trename (· + 1)
                  asimp at h ⊢
                  exact h)
      asimp at hC hn
      exact CongrTerm.proj hC hm hn
  | fix eA em ihA ihm =>
      intro τ τ' him hex
      asimp
      have hA := ihA τ τ' him (fun hr => nomatch hr)
      have hm := ihm (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr x hx => by
          cases x with
          | zero => asimp; exact CongrTerm.var
          | succ x =>
              have h := (hex hr x (by simp only [occursEx]; omega)).trename (· + 1)
              asimp at h ⊢
              exact h)
      asimp at hm
      exact CongrTerm.fix hA hm
  | unit => intro τ τ' _ _; asimp; exact CongrTerm.unit
  | one => intro τ τ' _ _; asimp; exact CongrTerm.one
  | bool => intro τ τ' _ _; asimp; exact CongrTerm.bool
  | tt => intro τ τ' _ _; asimp; exact CongrTerm.tt
  | ff => intro τ τ' _ _; asimp; exact CongrTerm.ff
  | ite eA em en1 en2 ihA ihm ihn1 ihn2 =>
      intro τ τ' him hex
      asimp
      have hA := ihA (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr => nomatch hr)
      have hm := ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega))
      have hn1 := ihn1 τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega))
      have hn2 := ihn2 τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega))
      asimp at hA
      exact CongrTerm.ite hA hm hn1 hn2
  | M eA ihA =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.M (ihA τ τ' him (fun hr => nomatch hr))
  | pure em ihm =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.pure (ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega)))
  | mlet em en ihm ihn =>
      intro τ τ' him hex
      asimp
      have hm := ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega))
      have hn := ihn (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr x hx => by
          cases x with
          | zero => asimp; exact CongrTerm.var
          | succ x =>
              have h := (hex hr x (by simp only [occursEx]; omega)).trename (· + 1)
              asimp at h ⊢
              exact h)
      asimp at hn
      exact CongrTerm.mlet hm hn
  | proto => intro τ τ' _ _; asimp; exact CongrTerm.proto
  | stop => intro τ τ' _ _; asimp; exact CongrTerm.stop
  | act eA eB ihA ihB =>
      intro τ τ' him hex
      asimp
      have hA := ihA τ τ' him (fun hr => nomatch hr)
      have hB := ihB (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr => nomatch hr)
      asimp at hB
      exact CongrTerm.act hA hB
  | ch eA ihA =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.ch (ihA τ τ' him (fun hr => nomatch hr))
  | chan_im =>
      intro τ τ' _ _
      asimp
      exact CongrTerm.chan_im
  | chan_ex =>
      intro τ τ' _ _
      asimp
      exact CongrTerm.chan_ex
  | fork eA em ihA ihm =>
      intro τ τ' him hex
      asimp
      have hA := ihA τ τ' him (fun hr => nomatch hr)
      have hm := ihm (up_Term_Term τ) (up_Term_Term τ') (congr_up_im him)
        (fun hr x hx => by
          cases x with
          | zero => asimp; exact CongrTerm.var
          | succ x =>
              have h := (hex hr x (by simp only [occursEx]; omega)).trename (· + 1)
              asimp at h ⊢
              exact h)
      asimp at hm
      exact CongrTerm.fork hA hm
  | recv em ihm =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.recv (ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega)))
  | send em ihm =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.send (ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega)))
  | close em ihm =>
      intro τ τ' him hex
      asimp
      exact CongrTerm.close (ihm τ τ' him
        (fun hr x hx => hex hr x (by simp only [occursEx]; omega)))
  | box => intro τ τ' _ _; asimp; exact CongrTerm.box


/-! ## Auxiliary typing inversions -/

/-- `fix` has no dynamic typing rule. -/
lemma _root_.TLLC.Dynamic.Typed.no_fix {Θ Γ Δ t B} (ty : Θ ⨾ Γ ⨾ Δ ⊢ t : B) :
    ∀ {A m}, t = .fix A m → False := by
  induction ty <;> intro A₀ m₀ e <;> try (cases e)
  case conv =>
    rename_i ih
    exact ih rfl

/-- The second component of a typed implicit pair is typed (at any pair type). -/
lemma pairIm_any_inv {Θ Γ Δ m n s C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .im s : C) :
    ∃ B, Θ ⨾ Γ ⨾ Δ ⊢ n : B := by
  generalize e : Term.pair m n .im s = x
  rw [e] at ty
  induction ty generalizing m n s
  case pairIm =>
    rename_i _ _ tyn _
    cases e; exact ⟨_, tyn⟩
  case conv =>
    rename_i _ _ _ ih
    exact ih e
  all_goals (exact absurd e (by simp))

/-- Both components of a typed explicit pair are typed (at any pair type). -/
lemma pairEx_any_inv {Θ Γ Δ m n s C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .ex s : C) :
    ∃ A B Θ1 Θ2 Δ1 Δ2,
      PMerge Θ1 Θ2 Θ ∧ Merge Δ1 Δ2 Δ ∧
      (Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : A) ∧ (Θ2 ⨾ Γ ⨾ Δ2 ⊢ n : B) := by
  generalize e : Term.pair m n .ex s = x
  rw [e] at ty
  induction ty generalizing m n s
  case pairEx =>
    rename_i mrgΘ mrgΔ _ tym tyn _ _
    cases e; exact ⟨_, _, _, _, _, _, mrgΘ, mrgΔ, tym, tyn⟩
  case conv =>
    rename_i _ _ _ ih
    exact ih e
  all_goals (exact absurd e (by simp))

/-- The scrutinee of a typed conditional is a typed boolean. -/
lemma ite_any_inv {Θ Γ Δ A m n1 n2 C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .ite A m n1 n2 : C) :
    ∃ Θ1 Δ1, Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : .bool := by
  generalize e : Term.ite A m n1 n2 = x
  rw [e] at ty
  induction ty generalizing A m n1 n2
  case ite =>
    rename_i tym _ _ _ _ _
    cases e; exact ⟨_, _, tym⟩
  case conv =>
    rename_i _ _ _ ih
    exact ih e
  all_goals (exact absurd e (by simp))

/-- Projection inversion: the scrutinee is a typed pair, and for an implicit pair the projection
continuation cannot use the first component explicitly. -/
lemma proj_any_inv {Θ Γ Δ C m n D}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .proj C m n : D) :
    ∃ A B i t Θ1 Δ1,
      (Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : .sig A B i t) ∧ (i = .im → occursEx 1 n = 0) := by
  generalize e : Term.proj C m n = x
  rw [e] at ty
  induction ty generalizing C m n
  case projIm =>
    rename_i tym tyn _ _
    cases e
    refine ⟨_, _, _, _, _, _, tym, fun _ => ?_⟩
    exact tyn.occursEx_zero 1 (NPos.succ NPos.zero)
  case projEx =>
    rename_i tym tyn _ _
    cases e
    exact ⟨_, _, _, _, _, _, tym, fun h => nomatch h⟩
  case conv =>
    rename_i _ _ _ ih
    exact ih e
  all_goals (exact absurd e (by simp))

/-- The type of an implicit pair converts to an implicit pair type. -/
lemma pairIm_ty_sig {Θ Γ Δ m n s C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .im s : C) :
    ∃ A B r, C ≃ Term.sig A B .im r := by
  generalize e : Term.pair m n .im s = x
  rw [e] at ty
  induction ty generalizing m n s
  case pairIm =>
    cases e
    exact ⟨_, _, _, ARS.Conv.refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, B0, r0, h⟩ := ih e
    exact ⟨A0, B0, r0, ARS.conv_trans (ARS.conv_sym eq1) h⟩
  all_goals (exact absurd e (by simp))

/-- An implicit pair cannot inhabit an explicit pair type. -/
lemma pairIm_sigEx_false {Θ Γ Δ m n s A B r}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .im s : .sig A B .ex r) : False := by
  obtain ⟨A0, B0, r0, h⟩ := pairIm_ty_sig ty
  obtain ⟨_, _, hre, _⟩ := Static.sig_inj h
  cases hre

/-! ## Values reflect through congruence -/

lemma val_thunk_congr_reflect {m' : Term} (hv : Val m') :
    ∀ m : Term, CongrTerm .ex m m' → Val m := by
  refine Val.rec
    (motive_1 := fun m' _ => ∀ m : Term, CongrTerm .ex m m' → Thunk m)
    (motive_2 := fun m' _ => ∀ m : Term, CongrTerm .ex m m' → Val m)
    ?mlet ?fork ?recv ?appSendIm ?appSendEx ?close
    ?var ?lam ?pairIm ?pairEx ?one ?tt ?ff ?pure ?chan ?send ?thunk hv
  case var =>
    intro x m e
    cases e
    exact Val.var
  case lam =>
    intro A body i s m e
    cases e
    exact Val.lam
  case pairIm =>
    intro m1 m2 s _ ih m e
    cases e with
    | pair em en => exact Val.pairIm (ih _ en)
  case pairEx =>
    intro m1 m2 s _ _ ih1 ih2 m e
    cases e with
    | pair em en => exact Val.pairEx (ih1 _ em) (ih2 _ en)
  case one =>
    intro m e
    cases e
    exact Val.one
  case tt =>
    intro m e
    cases e
    exact Val.tt
  case ff =>
    intro m e
    cases e
    exact Val.ff
  case pure =>
    intro v _ ih m e
    cases e with
    | pure ev => exact Val.pure (ih _ ev)
  case chan =>
    intro x m e
    cases e
    exact Val.chan
  case send =>
    intro c i m e
    cases e with
    | send em =>
        cases em
        exact Val.send
  case thunk =>
    intro t _ ih m e
    exact Val.thunk (ih m e)
  case mlet =>
    intro a b _ ih m e
    cases e with
    | mlet em en => exact Thunk.mlet (ih _ em)
  case fork =>
    intro A body m e
    cases e with
    | fork _ _ => exact Thunk.fork
  case recv =>
    intro c i m e
    cases e with
    | recv em =>
        cases em
        exact Thunk.recv
  case appSendIm =>
    intro c payload m e
    cases e with
    | app em en =>
        cases em with
        | send es =>
            cases es
            exact Thunk.appSendIm
  case appSendEx =>
    intro c v _ ih m e
    cases e with
    | app em en =>
        cases em with
        | send es =>
            cases es
            exact Thunk.appSendEx (ih _ en)
  case close =>
    intro b c m e
    cases e with
    | close em =>
        cases em
        exact Thunk.close

/-- Values reflect through congruence. -/
lemma Val.congr_reflect {m m' : Term} (e : CongrTerm .ex m m') (hv : Val m') : Val m :=
  val_thunk_congr_reflect hv m e

/-! ## Steps of typed terms reflect through congruence -/

/-- A single step of the congruent copy of a well-typed term reflects to a step of the term
itself, with congruent results. -/
lemma congrTerm_step_reflect {m' n' : Term} (st : m' ~>> n') :
    ∀ {Θ Γ Δ C m}, (Θ ⨾ Γ ⨾ Δ ⊢ m : C) → CongrTerm .ex m m' →
      ∃ n, (m ~>> n) ∧ CongrTerm .ex n n' := by
  induction st with
  | @appL a a' b i _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @app m₀ _ n₀ _ _ _ em en =>
          cases i with
          | im =>
              obtain ⟨A, B, s, tym, _, _⟩ := appIm_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.app na n₀ .im, Step.appL sta, .app ena en⟩
          | ex =>
              obtain ⟨A, B, s, Θ1, Θ2, Δ1, Δ2, _, _, tym, _, _⟩ := appEx_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.app na n₀ .ex, Step.appL sta, .app ena en⟩
  | @appR a b b' _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @app m₀ _ n₀ _ _ _ em en =>
          obtain ⟨A, B, s, Θ1, Θ2, Δ1, Δ2, _, _, _, tyn, _⟩ := appEx_inv ty
          obtain ⟨nb, stb, enb⟩ := ih tyn en
          exact ⟨.app m₀ nb .ex, Step.appR stb, .app em enb⟩
  | @betaIm A body p s =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @app f₀ _ p₀ _ _ _ ef ep =>
          cases ef with
          | @lam A₀ _ body₀ _ _ _ _ eA ebody =>
              obtain ⟨A1, B1, s1, tyf, _, _⟩ := appIm_inv ty
              have tybody := lamIm_inv tyf
              have hz : occursEx 0 body₀ = 0 :=
                tybody.occursEx_zero 0 NPos.zero
              refine ⟨body₀[Chan.var_Chan; p₀ .: Term.var_Term], Step.betaIm, ?_⟩
              refine congrTerm_tsubst_of_occursEx ebody
                (p₀ .: Term.var_Term) (p .: Term.var_Term)
                (fun x => ?_) (fun _ x hx => ?_)
              · cases x with
                | zero => exact ep
                | succ x => exact CongrTerm.var
              · cases x with
                | zero => exact absurd hx (by rw [hz]; simp)
                | succ x => exact CongrTerm.var
  | @betaEx A body p s hv =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @app f₀ _ p₀ _ _ _ ef ep =>
          cases ef with
          | @lam A₀ _ body₀ _ _ _ _ eA ebody =>
              refine ⟨body₀[Chan.var_Chan; p₀ .: Term.var_Term],
                Step.betaEx (Val.congr_reflect ep hv), ?_⟩
              refine congrTerm_tsubst_of_occursEx ebody
                (p₀ .: Term.var_Term) (p .: Term.var_Term)
                (fun x => ?_) (fun _ x hx => ?_)
              · cases x with
                | zero => exact ep.to_im
                | succ x => exact CongrTerm.var
              · cases x with
                | zero => exact ep
                | succ x => exact CongrTerm.var
  | @pairL a a' b s _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @pair m₀ _ n₀ _ _ _ _ em en =>
          obtain ⟨A, B, Θ1, Θ2, Δ1, Δ2, _, _, tym, _⟩ := pairEx_any_inv ty
          obtain ⟨na, sta, ena⟩ := ih tym em
          exact ⟨.pair na n₀ .ex s, Step.pairL sta, .pair ena en⟩
  | @pairR a b b' i s _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @pair m₀ _ n₀ _ _ _ _ em en =>
          cases i with
          | im =>
              obtain ⟨B, tyn⟩ := pairIm_any_inv ty
              obtain ⟨nb, stb, enb⟩ := ih tyn en
              exact ⟨.pair m₀ nb .im s, Step.pairR stb, .pair em enb⟩
          | ex =>
              obtain ⟨A, B, Θ1, Θ2, Δ1, Δ2, _, _, _, tyn⟩ := pairEx_any_inv ty
              obtain ⟨nb, stb, enb⟩ := ih tyn en
              exact ⟨.pair m₀ nb .ex s, Step.pairR stb, .pair em enb⟩
  | @projM A a a' n _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @proj C₀ _ m₀ _ n₀ _ _ eC em en =>
          obtain ⟨A1, B1, i, t, Θ1, Δ1, tym, _⟩ := proj_any_inv ty
          obtain ⟨na, sta, ena⟩ := ih tym em
          exact ⟨.proj C₀ na n₀, Step.projM sta, .proj eC ena en⟩
  | @projE A m1 m2 n i s hv =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @proj C₀ _ p₀ _ n₀ _ _ eC ep en =>
          cases ep with
          | @pair p1 _ p2 _ _ _ _ e1 e2 =>
              obtain ⟨A1, B1, i1, t, Θ1, Δ1, typ, him1⟩ := proj_any_inv ty
              refine ⟨n₀[Chan.var_Chan; p2 .: p1 .: Term.var_Term],
                Step.projE (Val.congr_reflect (.pair e1 e2) hv), ?_⟩
              refine congrTerm_tsubst_of_occursEx en
                (p2 .: p1 .: Term.var_Term) (m2 .: m1 .: Term.var_Term)
                (fun x => ?_) (fun _ x hx => ?_)
              · cases x with
                | zero => exact e2.to_im
                | succ x =>
                    cases x with
                    | zero => exact e1.to_im
                    | succ x => exact CongrTerm.var
              · cases x with
                | zero => exact e2
                | succ x =>
                    cases x with
                    | zero =>
                        cases i with
                        | ex => exact e1
                        | im =>
                            cases i1 with
                            | im => exact absurd hx (by rw [him1 rfl]; simp)
                            | ex => exact absurd typ pairIm_sigEx_false
                    | succ x => exact CongrTerm.var
  | @fixE A body =>
      intro Θ Γ Δ C m ty e
      cases e with
      | fix eA em => exact (ty.no_fix rfl).elim
  | @iteM A a a' n1 n2 _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @ite A₀ _ m₀ _ n1₀ _ n2₀ _ _ eA em en1 en2 =>
          obtain ⟨Θ1, Δ1, tym⟩ := ite_any_inv ty
          obtain ⟨na, sta, ena⟩ := ih tym em
          exact ⟨.ite A₀ na n1₀ n2₀, Step.iteM sta, .ite eA ena en1 en2⟩
  | @iteT A n1 n2 =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @ite A₀ _ m₀ _ n1₀ _ n2₀ _ _ eA em en1 en2 =>
          cases em
          exact ⟨n1₀, Step.iteT, en1⟩
  | @iteF A n1 n2 =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @ite A₀ _ m₀ _ n1₀ _ n2₀ _ _ eA em en1 en2 =>
          cases em
          exact ⟨n2₀, Step.iteF, en2⟩
  | @pure a a' _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @pure m₀ _ _ em =>
          obtain ⟨A, tym, _⟩ := pure_invX ty
          obtain ⟨na, sta, ena⟩ := ih tym em
          exact ⟨.pure na, Step.pure sta, .pure ena⟩
  | @mletL a a' b _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @mlet m₀ _ n₀ _ _ em en =>
          obtain ⟨Θ1, Θ2, Δ1, Δ2, A, B, s1, t, _, _, _, tym, _, _⟩ := mlet_invX ty
          obtain ⟨na, sta, ena⟩ := ih tym em
          exact ⟨.mlet na n₀, Step.mletL sta, .mlet ena en⟩
  | @mletE v b hv =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @mlet m₀ _ n₀ _ _ em en =>
          cases em with
          | @pure v₀ _ _ ev =>
              refine ⟨n₀[Chan.var_Chan; v₀ .: Term.var_Term],
                Step.mletE (Val.congr_reflect ev hv), ?_⟩
              refine congrTerm_tsubst_of_occursEx en
                (v₀ .: Term.var_Term) (v .: Term.var_Term)
                (fun x => ?_) (fun _ x hx => ?_)
              · cases x with
                | zero => exact ev.to_im
                | succ x => exact CongrTerm.var
              · cases x with
                | zero => exact ev
                | succ x => exact CongrTerm.var
  | @recv a a' i _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @recv m₀ _ _ _ em =>
          cases i with
          | im =>
              obtain ⟨r1, r2, A, B, _, _, tym⟩ := recvIm_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.recv na .im, Step.recv sta, .recv ena⟩
          | ex =>
              obtain ⟨r1, r2, A, B, _, _, tym⟩ := recvEx_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.recv na .ex, Step.recv sta, .recv ena⟩
  | @send a a' i _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @send m₀ _ _ _ em =>
          cases i with
          | im =>
              obtain ⟨r1, r2, A, B, _, _, tym⟩ := sendIm_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.send na .im, Step.send sta, .send ena⟩
          | ex =>
              obtain ⟨r1, r2, A, B, _, _, tym⟩ := sendEx_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.send na .ex, Step.send sta, .send ena⟩
  | @close b a a' _ ih =>
      intro Θ Γ Δ C m ty e
      cases e with
      | @close _ m₀ _ _ em =>
          cases b with
          | false =>
              obtain ⟨_, tym⟩ := wait_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.close false na, Step.close sta, .close ena⟩
          | true =>
              obtain ⟨_, tym⟩ := close_inv ty
              obtain ⟨na, sta, ena⟩ := ih tym em
              exact ⟨.close true na, Step.close sta, .close ena⟩

end TLLC.Process
