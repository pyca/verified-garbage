module
public import VerifiedGarbage.Spec.Ffdh

import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import Std.Data.DTreeMap.Internal.Balancing
import VerifiedGarbage.Proof.Framework.Omega

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
      rw [List.length_drop]; omega
    simp only [witnessStep, draw_of_le h, bind, Option.bind_some, pure]
    by_cases ha : 2 ≤ Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1) ∧
        Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1) < w - 1
    · simp [ha]
    · simp only [Bool.and_eq_true, decide_eq_true_eq, ha, ite_false, hd, ite_true]
      rfl
  · simp only [ite_eq_right h]
    simp only [witnessStep, draw_of_short (by omega : r.length < witnessOctets w), bind, Option.bind_none]

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
          rw [List.length_drop]; omega
        obtain ⟨u, hu, hul, hr⟩ := ih _ hd _ _ he
        refine ⟨witnessOctets w + u, by omega, ?_, ?_⟩
        · rw [List.length_drop] at hul; omega
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

/-- Once trial division has passed, this Boolean is the specified probable-prime result. -/
theorem checkWitnesses_probable {w : Nat} {r rest : Rand} {pass : Bool}
    (hs : primeShape w = true)
    (he : checkWitnesses w (primeChecks (bitLength w)) r = some (pass, rest)) :
    ∃ as, drawWitnesses w (primeChecks (bitLength w)) r = some (as, rest) ∧ probablePrime w as = pass := by
  rw [checkWitnesses_eq, Option.map_eq_some_iff] at he
  obtain ⟨⟨as, rest'⟩, ha, he⟩ := he
  simp only [Prod.mk.injEq] at he
  obtain ⟨hpass, rfl⟩ := he
  exact ⟨as, ha, (drawWitnesses_probable hs ha).trans hpass⟩

end VG.Proof.Ffdh.ParameterCandidate
