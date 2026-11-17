module

public import VerifiedGarbage.Spec.Ffdh
import Std.Data.DTreeMap.Internal.Balancing
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Generate

/-! ### `Ffdh.ParameterCandidate.Witness`, which this module and modules that import it used -/

section

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
      exact ⟨by simp only [List.length_cons]; omega_using [hlen], fun b he => by
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

end

end

/-! # FFDH parameter candidates: executable witness-stream equations -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

theorem draw_of_le {r : Rand} {len : Nat} (h : len ≤ r.length) :
    draw len r = some (Spec.Rsa.os2ip (r.take len), r.drop len) := by
  simp only [draw, List.length_take, Nat.min_eq_left h, ite_true]

theorem draw_of_short {r : Rand} {len : Nat} (h : r.length < len) : draw len r = none := by
  simp only [draw, List.length_take, Nat.min_eq_right (Nat.le_of_lt h), Nat.ne_of_lt h, ite_false]

/-- A nonempty draw either accepts this masked prefix or retries on its suffix. -/
theorem drawWitness_eq {w : Nat} (hn : 0 < witnessOctets w) (r : Rand) :
    drawWitness w r =
      if witnessOctets w ≤ r.length then
        let a := Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1)
        if 2 ≤ a ∧ a < w - 1 then some (a, r.drop (witnessOctets w))
        else drawWitness w (r.drop (witnessOctets w))
      else none := by
  rw [drawWitness, loop]
  by_cases h : witnessOctets w ≤ r.length
  · simp only [ite_eq_left h]
    have hd : (r.drop (witnessOctets w)).length < r.length := by
      rw [List.length_drop]; omega_using [hn, h]
    simp only [witnessStep, draw_of_le h, bind, Option.bind_some, pure]
    by_cases ha : 2 ≤ Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1) ∧
        Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1) < w - 1
    · simp [ha]
    · simp only [Bool.and_eq_true, decide_eq_true_eq, ha, ite_false, hd, ite_true]
      rfl
  · simp only [ite_eq_right h]
    simp only [witnessStep, draw_of_short (by omega_using [h] : r.length < witnessOctets w), bind, Option.bind_none]

/-- An accepted rejection-sampled witness consumes a nonempty prefix. -/
theorem drawWitness_suffix {w : Nat} (hn : 0 < witnessOctets w) :
    ∀ r a rest, drawWitness w r = some (a, rest) →
      ∃ u, 0 < u ∧ u ≤ r.length ∧ rest = r.drop u := by
  intro r
  induction r using (measure List.length).wf.induction with
  | h r ih =>
    intro a rest he
    rw [drawWitness_eq hn] at he
    split at he
    · rename_i hl
      dsimp only at he
      split at he
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        exact ⟨witnessOctets w, hn, hl, he.2.symm⟩
      · have hd : (r.drop (witnessOctets w)).length < r.length := by
          rw [List.length_drop]; omega_using [hn, hl]
        obtain ⟨u, hu, hul, hr⟩ := ih _ hd _ _ he
        refine ⟨witnessOctets w + u, by omega_using [hn], ?_, ?_⟩
        · rw [List.length_drop] at hul; omega_using [hl, hul]
        · rw [hr, List.drop_drop]
    · cases he

/-- The machine needs only the conjunction of rounds, rather than a list
of witnesses. This recursion retains the specification's exact tape use. -/
def checkWitnesses (w : Nat) : Nat → Rand → Option (Bool × Rand)
  | 0, r => some (true, r)
  | n + 1, r => do
    let (a, r) ← drawWitness w r
    if mrRound w a then checkWitnesses w n r else some (false, r)

theorem checkWitnesses_eq (w : Nat) : ∀ n r,
    checkWitnesses w n r = (drawWitnesses w n r).map (fun x => (x.1.all (mrRound w), x.2)) := by
  intro n
  induction n with
  | zero => intro r; rfl
  | succ n ih =>
    intro r
    simp only [checkWitnesses, drawWitnesses]
    cases hd : drawWitness w r with
    | none => rfl
    | some ar =>
      obtain ⟨a, rest⟩ := ar
      simp only [bind, Option.bind_some]
      by_cases hm : mrRound w a = true
      · simp only [hm, ite_true, ih]
        cases drawWitnesses w n rest with
        | none => rfl
        | some ar =>
          obtain ⟨as, rest'⟩ := ar
          simp only [Option.map_some, Option.bind_some, pure, List.all_cons, hm, Bool.true_and]
      · have hf : mrRound w a = false := Bool.eq_false_iff.mpr hm
        simp [hf]

end VG.Proof.Ffdh.ParameterCandidate
