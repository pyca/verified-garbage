module

public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates: rejection-sampled witness streams -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

/-- Every accepted draw is in the specified uniform witness interval. -/
theorem witnessStep_bounds {w a : Nat} {r r' : Rand}
    (h : witnessStep w () r = some (.inl a, r')) : 2 ≤ a ∧ a < w - 1 := by
  simp only [witnessStep, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x, rest⟩, _, h⟩ := h
  dsimp only at h
  split at h
  · rename_i hb
    simp only [pure, Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq] at h
    obtain ⟨ha, _⟩ := h
    subst ha
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
  · simp [pure] at h

theorem drawWitness_bounds {w a : Nat} {r r' : Rand}
    (h : drawWitness w r = some (a, r')) : 2 ≤ a ∧ a < w - 1 := by
  exact VG.Proof.RsaKeyGen.loop_inl (fun a => 2 ≤ a ∧ a < w - 1)
    (fun _ _ _ _ he => witnessStep_bounds he) () r a r' h

/-- A stream draws at most the requested number of witnesses, and all are in range. -/
theorem drawWitnesses_bounds {w : Nat} : ∀ n r as r', drawWitnesses w n r = some (as, r') →
    as.length ≤ n ∧ ∀ a ∈ as, 2 ≤ a ∧ a < w - 1 := by
  intro n
  induction n with
  | zero =>
    intro r as r' h
    simp only [drawWitnesses, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simp
  | succ n ih =>
    intro r as r' h
    simp only [drawWitnesses, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, rest⟩, ha, h⟩ := h
    have hb := drawWitness_bounds ha
    dsimp only at h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨bs, rest'⟩, hbs, h⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      obtain ⟨hlen, hall⟩ := ih _ _ _ hbs
      exact ⟨by simp only [List.length_cons]; omega, fun b he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hb
        · exact hall b he⟩
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨by simp, fun b he => by simpa only [List.mem_singleton.mp he] using hb⟩

/-- A stream on which every round passes has consumed exactly the requested count. -/
theorem drawWitnesses_pass_count {w : Nat} : ∀ n r as r', drawWitnesses w n r = some (as, r') →
    as.all (mrRound w) = true → as.length = n := by
  intro n
  induction n with
  | zero =>
    intro r as r' h _
    simp only [drawWitnesses, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rfl
  | succ n ih =>
    intro r as r' h hall
    simp only [drawWitnesses, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, rest⟩, _, h⟩ := h
    dsimp only at h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨bs, rest'⟩, hbs, h⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      have hb := (Bool.and_eq_true _ _).mp hall
      simp only [List.length_cons, ih _ _ _ hbs hb.2]
    · rename_i hf
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
      exact False.elim (hf hall)

/-- After the shape checks, passing the requested stream is exactly probablePrime. -/
theorem drawWitnesses_probable {w : Nat} {r r' : Rand} {as : List Nat}
    (hs : primeShape w = true)
    (h : drawWitnesses w (primeChecks (Spec.RsaKeyGen.bitLength w)) r = some (as, r')) :
    probablePrime w as = as.all (mrRound w) := by
  have hb := (drawWitnesses_bounds _ _ _ _ h).2
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hp
    simp only [probablePrime, Bool.and_eq_true] at hp
    apply List.all_eq_true.mpr
    intro a ha
    have hf := List.all_eq_true.mp hp.2 a ha
    exact ((Bool.and_eq_true _ _).mp hf).2
  · intro hp
    have hn := drawWitnesses_pass_count _ _ _ _ h hp
    simp only [probablePrime, hs, hn, beq_self_eq_true, Bool.true_and]
    apply List.all_eq_true.mpr
    intro a ha
    have hbounds := hb a ha
    have hr := List.all_eq_true.mp hp a ha
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hbounds.1, hbounds.2⟩, hr⟩

end VG.Proof.Ffdh.ParameterCandidate
