module

public import VerifiedGarbage.Proof.RsaKeyGen.MrIter
import VerifiedGarbage.Proof.RsaKeyGen.MrCounts

/-!
# Miller–Rabin witness by witness, for any checks and any first offset

`MrLoopAt c ch a m L s r k n` is `MrAt` (`MrIter.lean`) generalized two
ways, so that the same loop serves RSA's `primalityTest` and DSA's
probable-prime test (`Spec.Dsa.probablePrime`):

* it is stated over the loop of `mrStep` with `ch` uniform checks,
  `loop (mrStep c ch a m) (1, 0)`, rather than over `primalityTest`, whose
  checks are RSA's `checksForSize` (DSA's are `primeChecks`);
* the witnesses are drawn from offset `s` of `r` on, the `k`-th (from 0) at
  `s + L k` (`mrSB`), rather than after the candidate's own `L` octets: RSA's
  tape starts with the candidate (`s = L`), DSA's holds witnesses alone
  (`s = 0`).

`MrLoopAt.toMrAt` and `MrAt.toMrLoopAt` convert to and from `MrAt` for
`s = L` when the primality test is that loop.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-- The counts after `k` witnesses passed, the first drawn at offset `s`. -/
def mrSB (c L s : Nat) (r : Rand) : Nat → Nat × Nat
  | 0 => (1, 0)
  | k + 1 => ((mrSB c L s r k).1 + 1, (mrSB c L s r k).2 + if (wit c L r (s + L * k)).2 then 1 else 0)

theorem mrSB_eq_mrS (c L : Nat) (r : Rand) : ∀ k, mrSB c L L r k = mrS c L r k
  | 0 => rfl
  | k + 1 => by
    rw [mrSB, mrS, mrSB_eq_mrS c L r k, show L + L * k = L * (k + 1) by rw [Nat.mul_succ]; omega]

theorem mrSB_first (c L s : Nat) (r : Rand) : ∀ k, (mrSB c L s r k).1 = k + 1
  | 0 => rfl
  | k + 1 => by rw [mrSB, mrSB_first c L s r k]

theorem mrSB_uniform_le (c L s : Nat) (r : Rand) : ∀ k, (mrSB c L s r k).2 ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have ih := mrSB_uniform_le c L s r k
    rw [mrSB]
    split <;> omega

theorem mrSB_uniform_next (c L s : Nat) (r : Rand) (k : Nat) :
    (mrSB c L s r (k + 1)).2 = (mrSB c L s r k).2 + (wit c L r (s + L * k)).2.toNat := by
  rw [mrSB]
  cases (wit c L r (s + L * k)).2 <;> rfl

/-- After `k` witnesses passed, with `n + 1` iterations left. -/
structure MrLoopAt (c ch a m L s : Nat) (r : Rand) (k n : Nat) : Prop where
  run : loop (mrStep c ch a m) (1, 0) (r.drop s) = loop (mrStep c ch a m) (mrSB c L s r k) (r.drop (s + L * k))
  go : goS ch (mrSB c L s r k)
  iters : itersOf L r.length (shapeOf (loop (mrStep c ch a m) (1, 0) (r.drop s))) (s + L * k) = n + 1
  used : s + L * k ≤ r.length

section
variable {c ch a m L s : Nat} {r : Rand} {k n : Nat}

/-- The witness passes and more are needed. -/
theorem mrLoopAt_next (h : MrLoopAt c ch a m L s r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : s + L * k + L ≤ r.length) (hp : mrIteration c a m (wit c L r (s + L * k)).1 = true)
    (hg : goS ch (mrSB c L s r (k + 1))) : 0 < n ∧ MrLoopAt c ch a m L s r (k + 1) (n - 1) := by
  have e := mrLoop_step c ch a m L r (mrSB c L s r k).1 (mrSB c L s r k).2 (s + L * k) h.go hwb hL
  rw [ite_t hav] at e
  unfold wit at hp
  rw [ite_t hp] at e
  have hk : s + L * k + L = s + L * (k + 1) := by rw [Nat.mul_succ]; omega
  rw [hk] at e
  have l1 : loop (mrStep c ch a m) (1, 0) (r.drop s) =
      loop (mrStep c ch a m) (mrSB c L s r (k + 1)) (r.drop (s + L * (k + 1))) := by
    rw [h.run, e]; rfl
  have ic := iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r) (i := (mrSB c L s r (k + 1)).1)
    (uni := (mrSB c L s r (k + 1)).2) (u := s + L * (k + 1)) hg hwb hL (by rw [Nat.mul_succ]; omega)
    (by rw [← hk]; omega)
  rw [← l1, show s + L * (k + 1) - L = s + L * k by rw [Nat.mul_succ]; omega, h.iters] at ic
  exact ⟨by omega, ⟨l1, hg, by omega, by rw [← hk]; omega⟩⟩

/-- The witness passes and no more are needed: `c` is probably prime. -/
theorem mrLoopAt_done (h : MrLoopAt c ch a m L s r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : s + L * k + L ≤ r.length) (hp : mrIteration c a m (wit c L r (s + L * k)).1 = true)
    (hg : ¬ goS ch (mrSB c L s r (k + 1))) :
    n = 0 ∧ loop (mrStep c ch a m) (1, 0) (r.drop s) = some (true, r.drop (s + L * k + L)) := by
  have e := mrLoop_step c ch a m L r (mrSB c L s r k).1 (mrSB c L s r k).2 (s + L * k) h.go hwb hL
  rw [ite_t hav] at e
  unfold wit at hp
  rw [ite_t hp] at e
  have d := mrLoop_done c ch a m (r.drop (s + L * k + L)) (mrSB c L s r (k + 1)).1 (mrSB c L s r (k + 1)).2 hg
  have l1 : loop (mrStep c ch a m) (1, 0) (r.drop s) = some (true, r.drop (s + L * k + L)) := by
    rw [h.run, e]; exact d
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (s + L * k + L)) - (s + L * k) = L by omega, Nat.div_self hL] at this
  omega

/-- The witness fails: `c` is composite. -/
theorem mrLoopAt_fail (h : MrLoopAt c ch a m L s r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : s + L * k + L ≤ r.length) (hp : mrIteration c a m (wit c L r (s + L * k)).1 = false) :
    n = 0 ∧ loop (mrStep c ch a m) (1, 0) (r.drop s) = some (false, r.drop (s + L * k + L)) := by
  have e := mrLoop_step c ch a m L r (mrSB c L s r k).1 (mrSB c L s r k).2 (s + L * k) h.go hwb hL
  rw [ite_t hav] at e
  unfold wit at hp
  rw [ite_f (by simp [hp])] at e
  have l1 : loop (mrStep c ch a m) (1, 0) (r.drop s) = some (false, r.drop (s + L * k + L)) := by
    rw [h.run, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (s + L * k + L)) - (s + L * k) = L by omega, Nat.div_self hL] at this
  omega

/-- Too few octets left for the witness. -/
theorem mrLoopAt_short (h : MrLoopAt c ch a m L s r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : ¬ s + L * k + L ≤ r.length) : n = 0 ∧ loop (mrStep c ch a m) (1, 0) (r.drop s) = none := by
  have e := mrLoop_step c ch a m L r (mrSB c L s r k).1 (mrSB c L s r k).2 (s + L * k) h.go hwb hL
  rw [ite_f hav] at e
  have l1 : loop (mrStep c ch a m) (1, 0) (r.drop s) = none := by rw [h.run, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_none, itersOf] at this
  rw [Nat.div_eq_of_lt (by omega)] at this
  omega

/-- The start. -/
theorem mrLoopAt_zero (hwb : witnessBytes c = L) (hL : 0 < L) (hu : s ≤ r.length) :
    MrLoopAt c ch a m L s r 0 (itersOf L r.length (shapeOf (loop (mrStep c ch a m) (1, 0) (r.drop s))) s - 1) := by
  have hg : goS ch (mrSB c L s r 0) := .inl (by simp [mrSB, blindedChecks])
  refine ⟨by simp [mrSB], hg, ?_, by omega⟩
  rw [Nat.mul_zero, Nat.add_zero]
  suffices 1 ≤ itersOf L r.length (shapeOf (loop (mrStep c ch a m) (1, 0) (r.drop s))) s by omega
  rcases e : loop (mrStep c ch a m) (1, 0) (r.drop s) with _ | ⟨b, rest⟩
  · simp only [shapeOf, Option.map_none, itersOf]; exact Nat.le_add_left 1 _
  · have := mrLoop_rest (Or.inl (by decide)) hwb hL e
    simp only [shapeOf, Option.map_some, itersOf]
    exact (Nat.le_div_iff_mul_le hL).mpr (by omega)

/-- `MrAt` is `MrLoopAt` from offset `L` when the primality test is the
loop with the checks `ch`. -/
theorem MrLoopAt.toMrAt (hc : primalityTest c (r.drop L) = loop (mrStep c ch a m) (1, 0) (r.drop L))
    (h : MrLoopAt c ch a m L L r k n) : MrAt c ch a m L r k n := by
  have e : L + L * k = L * (k + 1) := by rw [Nat.mul_succ]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc, h.run, mrSB_eq_mrS, e]
  · rw [← mrSB_eq_mrS]; exact h.go
  · rw [hc, ← e]; exact h.iters
  · rw [← e]; exact h.used

theorem MrAt.toMrLoopAt (hc : primalityTest c (r.drop L) = Spec.RsaKeyGen.loop (mrStep c ch a m) (1, 0) (r.drop L))
    (h : MrAt c ch a m L r k n) : MrLoopAt c ch a m L L r k n := by
  have e : L + L * k = L * (k + 1) := by rw [Nat.mul_succ]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hc, h.loop, mrSB_eq_mrS, e]
  · rw [mrSB_eq_mrS]; exact h.go
  · rw [← hc, e]; exact h.iters
  · rw [e]; exact h.used

end

end VG.Proof.RsaKeyGen
