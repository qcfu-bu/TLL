import TLLC.Dynamic.Step

/-!
# Reflection of dynamic reduction under channel renaming

Channel renamings substitute channel variables for channel variables, so they can neither create
nor destroy any redex: values, thunks, and single steps of a renamed term reflect back to the
original term. These are the term-level inversion principles used by the reflection theorem
(`TLLC/Spawning/Reflection.lean`) to replay a machine step, fired on a renamed thread of a
flattened spawning tree, on the underlying node body.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation

lemma val_thunk_cren_reflect {ξ : Nat → Nat} {m' : Term} (hv : Val m') :
    ∀ m : Term, m' = m⟨ξ; (id : Nat → Nat)⟩ → Val m := by
  refine Val.rec
    (motive_1 := fun m' _ => ∀ m : Term, m' = m⟨ξ; (id : Nat → Nat)⟩ → Thunk m)
    (motive_2 := fun m' _ => ∀ m : Term, m' = m⟨ξ; (id : Nat → Nat)⟩ → Val m)
    ?mlet ?fork ?recv ?appSendIm ?appSendEx ?close
    ?var ?lam ?pairIm ?pairEx ?one ?tt ?ff ?pure ?chan ?send ?thunk hv
  case var =>
    intro x m hm
    cases m <;> asimp at hm <;> try simp at hm
    exact Val.var
  case lam =>
    intro A body i s m hm
    cases m <;> asimp at hm <;> try simp at hm
    exact Val.lam
  case pairIm =>
    intro m1 m2 s _ ih m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a b r s' =>
      obtain ⟨h1, h2, hr, hs⟩ := hm
      subst hr
      exact Val.pairIm (ih _ h2)
  case pairEx =>
    intro m1 m2 s _ _ ih1 ih2 m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a b r s' =>
      obtain ⟨h1, h2, hr, hs⟩ := hm
      subst hr
      exact Val.pairEx (ih1 _ h1) (ih2 _ h2)
  case one =>
    intro m hm
    cases m <;> asimp at hm <;> try simp at hm
    exact Val.one
  case tt =>
    intro m hm
    cases m <;> asimp at hm <;> try simp at hm
    exact Val.tt
  case ff =>
    intro m hm
    cases m <;> asimp at hm <;> try simp at hm
    exact Val.ff
  case pure =>
    intro v _ ih m hm
    cases m <;> asimp at hm <;> try simp at hm
    next v₀ =>
      exact Val.pure (ih _ hm)
  case chan =>
    intro x m hm
    cases m <;> asimp at hm <;> try simp at hm
    next c₀ =>
      cases c₀
      exact Val.chan
  case send =>
    intro c i m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a r₀ =>
      obtain ⟨h1, hr⟩ := hm
      subst hr
      cases a <;> asimp at h1 <;> try simp at h1
      next c₀ =>
        cases c₀
        exact Val.send
  case thunk =>
    intro t _ ih m hm
    exact Val.thunk (ih m hm)
  case mlet =>
    intro a b _ ih m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a₀ b₀ =>
      exact Thunk.mlet (ih _ hm.1)
  case fork =>
    intro A body m hm
    cases m <;> asimp at hm <;> try simp at hm
    exact Thunk.fork
  case recv =>
    intro c i m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a r₀ =>
      obtain ⟨h1, hr⟩ := hm
      subst hr
      cases a <;> asimp at h1 <;> try simp at h1
      next c₀ =>
        cases c₀
        exact Thunk.recv
  case appSendIm =>
    intro c payload m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a b r₀ =>
      obtain ⟨h1, h2, hr⟩ := hm
      subst hr
      cases a <;> asimp at h1 <;> try simp at h1
      next s₀ r₁ =>
        obtain ⟨hs, hi⟩ := h1
        subst hi
        cases s₀ <;> asimp at hs <;> try simp at hs
        next c₀ =>
          cases c₀
          exact Thunk.appSendIm
  case appSendEx =>
    intro c v _ ih m hm
    cases m <;> asimp at hm <;> try simp at hm
    next a b r₀ =>
      obtain ⟨h1, h2, hr⟩ := hm
      subst hr
      cases a <;> asimp at h1 <;> try simp at h1
      next s₀ r₁ =>
        obtain ⟨hs, hi⟩ := h1
        subst hi
        cases s₀ <;> asimp at hs <;> try simp at hs
        next c₀ =>
          cases c₀
          exact Thunk.appSendEx (ih _ h2)
  case close =>
    intro b c m hm
    cases m <;> asimp at hm <;> try simp at hm
    next b₀ a =>
      obtain ⟨hb, h1⟩ := hm
      subst hb
      cases a <;> asimp at h1 <;> try simp at h1
      next c₀ =>
        cases c₀
        exact Thunk.close

/-- Values reflect under channel renaming. -/
lemma Val.cren_reflect {ξ : Nat → Nat} {m : Term}
    (hv : Val (m⟨ξ; (id : Nat → Nat)⟩)) : Val m :=
  val_thunk_cren_reflect hv m rfl

private lemma scons_cren (v : Term) (ξ : Nat → Nat) :
    (fun x => ((v .: Term.var_Term) x)⟨ξ; (id : Nat → Nat)⟩) =
      ((v⟨ξ; (id : Nat → Nat)⟩) .: Term.var_Term) := by
  funext x
  cases x <;> (asimp; try simp)

private lemma scons2_cren (v w : Term) (ξ : Nat → Nat) :
    (fun x => ((v .: w .: Term.var_Term) x)⟨ξ; (id : Nat → Nat)⟩) =
      ((v⟨ξ; (id : Nat → Nat)⟩) .: (w⟨ξ; (id : Nat → Nat)⟩) .: Term.var_Term) := by
  funext x
  cases x with
  | zero => asimp
  | succ x => cases x <;> (asimp; try simp)

/-- Channel renaming commutes with term substitution (channels have no term binders). -/
private lemma csubst_cren_comm (body : Term) (τ : Nat → Term) (ξ : Nat → Nat) :
    (body[Chan.var_Chan; τ])⟨ξ; (id : Nat → Nat)⟩ =
      (body⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
        fun x => (τ x)⟨ξ; (id : Nat → Nat)⟩] := by
  asimp

/-- Single steps reflect under channel renaming. -/
lemma step_cren_reflect {ξ : Nat → Nat} {m' n' : Term} (st : m' ~>> n') :
    ∀ m : Term, m' = m⟨ξ; (id : Nat → Nat)⟩ →
      ∃ n, (m ~>> n) ∧ n' = n⟨ξ; (id : Nat → Nat)⟩ := by
  induction st with
  | @appL a a' b i _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ i₀ =>
        obtain ⟨h1, h2, hi⟩ := hm
        subst hi
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ h1
        refine ⟨.app n₀ b₀ i, Step.appL st₀, ?_⟩
        asimp
        rw [hn, h2]
  | @appR a b b' _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ i₀ =>
        obtain ⟨h1, h2, hi⟩ := hm
        subst hi
        obtain ⟨n₀, st₀, hn⟩ := ih b₀ h2
        refine ⟨.app a₀ n₀ .ex, Step.appR st₀, ?_⟩
        asimp
        rw [hn, h1]
  | @betaIm A body n s =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ i₀ =>
        obtain ⟨h1, h2, hi⟩ := hm
        subst hi
        cases a₀ <;> asimp at h1 <;> try simp at h1
        next A₀ body₀ i₁ s₁ =>
          obtain ⟨hA, hbody, hi₁, hs⟩ := h1
          subst hi₁
          subst hs
          refine ⟨body₀[Chan.var_Chan; b₀ .: Term.var_Term], Step.betaIm, ?_⟩
          rw [csubst_cren_comm, scons_cren, hbody, h2]
          rfl
  | @betaEx A body v s hv =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ i₀ =>
        obtain ⟨h1, h2, hi⟩ := hm
        subst hi
        cases a₀ <;> asimp at h1 <;> try simp at h1
        next A₀ body₀ i₁ s₁ =>
          obtain ⟨hA, hbody, hi₁, hs⟩ := h1
          subst hi₁
          subst hs
          subst h2
          refine ⟨body₀[Chan.var_Chan; b₀ .: Term.var_Term],
            Step.betaEx (Val.cren_reflect hv), ?_⟩
          rw [csubst_cren_comm, scons_cren, hbody]
          rfl
  | @pairL a a' b s _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ i₀ s₀ =>
        obtain ⟨h1, h2, hi, hs⟩ := hm
        subst hi
        subst hs
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ h1
        refine ⟨.pair n₀ b₀ .ex s, Step.pairL st₀, ?_⟩
        asimp
        rw [hn, h2]
  | @pairR a b b' i s _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ i₀ s₀ =>
        obtain ⟨h1, h2, hi, hs⟩ := hm
        subst hi
        subst hs
        obtain ⟨n₀, st₀, hn⟩ := ih b₀ h2
        refine ⟨.pair a₀ n₀ i s, Step.pairR st₀, ?_⟩
        asimp
        rw [hn, h1]
  | @projM A a a' n _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next A₀ a₀ n₀ =>
        obtain ⟨hA, h1, h2⟩ := hm
        obtain ⟨p₀, st₀, hp⟩ := ih a₀ h1
        refine ⟨.proj A₀ p₀ n₀, Step.projM st₀, ?_⟩
        asimp
        rw [hA, hp, h2]
  | @projE A m1 m2 n i s hv =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next A₀ a₀ n₀ =>
        obtain ⟨hA, h1, h2⟩ := hm
        cases a₀ <;> asimp at h1 <;> try simp at h1
        next p1 p2 i₀ s₀ =>
          obtain ⟨hp1, hp2, hi, hs⟩ := h1
          subst hi
          subst hs
          refine ⟨n₀[Chan.var_Chan; p2 .: p1 .: Term.var_Term], ?_, ?_⟩
          · refine Step.projE (Val.cren_reflect (ξ := ξ) (m := .pair p1 p2 i s) ?_)
            asimp
            rw [← hp1, ← hp2]
            exact hv
          · rw [csubst_cren_comm, scons2_cren, hp1, hp2, h2]
  | @fixE A body =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next A₀ body₀ =>
        obtain ⟨hA, hbody⟩ := hm
        subst hA
        subst hbody
        refine ⟨body₀[Chan.var_Chan; (.fix A₀ body₀) .: Term.var_Term], Step.fixE, ?_⟩
        rw [csubst_cren_comm, scons_cren]
        asimp
  | @iteM A a a' n1 n2 _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next A₀ a₀ n1₀ n2₀ =>
        obtain ⟨hA, h1, h2, h3⟩ := hm
        obtain ⟨c₀, st₀, hc⟩ := ih a₀ h1
        refine ⟨.ite A₀ c₀ n1₀ n2₀, Step.iteM st₀, ?_⟩
        asimp
        rw [hA, hc, h2, h3]
  | @iteT A n1 n2 =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next A₀ a₀ n1₀ n2₀ =>
        obtain ⟨hA, h1, h2, h3⟩ := hm
        cases a₀ <;> asimp at h1 <;> try simp at h1
        exact ⟨n1₀, Step.iteT, h2⟩
  | @iteF A n1 n2 =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next A₀ a₀ n1₀ n2₀ =>
        obtain ⟨hA, h1, h2, h3⟩ := hm
        cases a₀ <;> asimp at h1 <;> try simp at h1
        exact ⟨n2₀, Step.iteF, h3⟩
  | @pure a a' _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ =>
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ hm
        refine ⟨.pure n₀, Step.pure st₀, ?_⟩
        asimp
        rw [hn]
  | @mletL a a' b _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ =>
        obtain ⟨h1, h2⟩ := hm
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ h1
        refine ⟨.mlet n₀ b₀, Step.mletL st₀, ?_⟩
        asimp
        rw [hn, h2]
  | @mletE v b hv =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ b₀ =>
        obtain ⟨h1, h2⟩ := hm
        cases a₀ <;> asimp at h1 <;> try simp at h1
        next v₀ =>
          subst h1
          refine ⟨b₀[Chan.var_Chan; v₀ .: Term.var_Term],
            Step.mletE (Val.cren_reflect hv), ?_⟩
          rw [csubst_cren_comm, scons_cren, h2]
          rfl
  | @recv a a' i _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ i₀ =>
        obtain ⟨h1, hi⟩ := hm
        subst hi
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ h1
        refine ⟨.recv n₀ i, Step.recv st₀, ?_⟩
        asimp
        rw [hn]
  | @send a a' i _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next a₀ i₀ =>
        obtain ⟨h1, hi⟩ := hm
        subst hi
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ h1
        refine ⟨.send n₀ i, Step.send st₀, ?_⟩
        asimp
        rw [hn]
  | @close b a a' _ ih =>
      intro m hm
      cases m <;> asimp at hm <;> try simp at hm
      next b₀ a₀ =>
        obtain ⟨hb, h1⟩ := hm
        subst hb
        obtain ⟨n₀, st₀, hn⟩ := ih a₀ h1
        refine ⟨.close b n₀, Step.close st₀, ?_⟩
        asimp
        rw [hn]

/-- Single steps reflect under channel renaming. -/
lemma Step.cren_reflect {ξ : Nat → Nat} {m n' : Term}
    (st : (m⟨ξ; (id : Nat → Nat)⟩) ~>> n') :
    ∃ n, (m ~>> n) ∧ n' = n⟨ξ; (id : Nat → Nat)⟩ :=
  step_cren_reflect st m rfl

end TLLC.Dynamic
