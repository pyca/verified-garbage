module

public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# A candidate for an RSA prime: Miller–Rabin, witness by witness

`mrS c L r k`: the counts `(i, uniform)` of `BN_primality_test`'s loop after
`k` witnesses passed, the `k`-th drawn at offset `L (k + 1)` of `r` (the
candidate's octets first). `MrAt … k n`: the loop from the start is the loop
from there, it draws again, and `n + 1` iterations of an implementation that
also counts the last, failing, draw are left (`itersOf`). A witness that is
drawn and passes leads to `MrAt … (k + 1) (n − 1)` if more are needed
(`mrAt_next`); otherwise the loop's result is known and `n = 0`
(`mrAt_done`, `mrAt_fail`, `mrAt_short`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-- The witness drawn at offset `u`. -/
def wit (c L : Nat) (r : Rand) (u : Nat) : Nat × Bool := witness (c - 1) (os2ip (seg r u L))

/-- The counts after `k` witnesses passed. -/
def mrS (c L : Nat) (r : Rand) : Nat → Nat × Nat
  | 0 => (1, 0)
  | k + 1 => ((mrS c L r k).1 + 1, (mrS c L r k).2 + if (wit c L r (L * (k + 1))).2 then 1 else 0)

/-- Whether the loop draws another witness. -/
def goS (ch : Nat) (s : Nat × Nat) : Prop := s.1 ≤ blindedChecks ∨ s.2 < ch

/-- After `k` witnesses passed, with `n + 1` iterations left. -/
structure MrAt (c ch a m L : Nat) (r : Rand) (k n : Nat) : Prop where
  loop : primalityTest c (r.drop L) = loop (mrStep c ch a m) (mrS c L r k) (r.drop (L * (k + 1)))
  go : goS ch (mrS c L r k)
  iters : itersOf L r.length (shapeOf (primalityTest c (r.drop L))) (L * (k + 1)) = n + 1
  used : L * (k + 1) ≤ r.length

section
variable {c ch a m L : Nat} {r : Rand} {k n : Nat}

/-- The witness passes and more are needed. -/
theorem mrAt_next (h : MrAt c ch a m L r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : L * (k + 1) + L ≤ r.length) (hp : mrIteration c a m (wit c L r (L * (k + 1))).1 = true)
    (hg : goS ch (mrS c L r (k + 1))) : 0 < n ∧ MrAt c ch a m L r (k + 1) (n - 1) := by
  have e := mrLoop_step c ch a m L r (mrS c L r k).1 (mrS c L r k).2 (L * (k + 1)) h.go hwb hL
  rw [ite_t hav] at e
  unfold wit at hp
  rw [ite_t hp] at e
  have hk : L * (k + 1) + L = L * (k + 1 + 1) := (Nat.mul_succ L (k + 1)).symm
  rw [hk] at e
  have l1 : primalityTest c (r.drop L) = loop (mrStep c ch a m) (mrS c L r (k + 1)) (r.drop (L * (k + 1 + 1))) := by
    rw [h.loop, e]; rfl
  have ic := iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r) (i := (mrS c L r (k + 1)).1)
    (uni := (mrS c L r (k + 1)).2) (u := L * (k + 1 + 1)) hg hwb hL (by rw [Nat.mul_succ]; omega) (by omega)
  rw [← l1, show L * (k + 1 + 1) - L = L * (k + 1) by rw [Nat.mul_succ]; omega, h.iters] at ic
  exact ⟨by omega, ⟨l1, hg, by omega, by omega⟩⟩

/-- The witness passes and no more are needed: `c` is probably prime. -/
theorem mrAt_done (h : MrAt c ch a m L r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : L * (k + 1) + L ≤ r.length) (hp : mrIteration c a m (wit c L r (L * (k + 1))).1 = true)
    (hg : ¬ goS ch (mrS c L r (k + 1))) :
    n = 0 ∧ primalityTest c (r.drop L) = some (true, r.drop (L * (k + 1) + L)) := by
  have e := mrLoop_step c ch a m L r (mrS c L r k).1 (mrS c L r k).2 (L * (k + 1)) h.go hwb hL
  rw [ite_t hav] at e
  unfold wit at hp
  rw [ite_t hp] at e
  have d := mrLoop_done c ch a m (r.drop (L * (k + 1) + L)) (mrS c L r (k + 1)).1 (mrS c L r (k + 1)).2 hg
  have l1 : primalityTest c (r.drop L) = some (true, r.drop (L * (k + 1) + L)) := by
    rw [h.loop, e]; exact d
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (L * (k + 1) + L)) - L * (k + 1) = L by omega, Nat.div_self hL] at this
  omega

/-- The witness fails: `c` is composite. -/
theorem mrAt_fail (h : MrAt c ch a m L r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : L * (k + 1) + L ≤ r.length) (hp : mrIteration c a m (wit c L r (L * (k + 1))).1 = false) :
    n = 0 ∧ primalityTest c (r.drop L) = some (false, r.drop (L * (k + 1) + L)) := by
  have e := mrLoop_step c ch a m L r (mrS c L r k).1 (mrS c L r k).2 (L * (k + 1)) h.go hwb hL
  rw [ite_t hav] at e
  unfold wit at hp
  rw [ite_f (by simp [hp])] at e
  have l1 : primalityTest c (r.drop L) = some (false, r.drop (L * (k + 1) + L)) := by rw [h.loop, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (L * (k + 1) + L)) - L * (k + 1) = L by omega, Nat.div_self hL] at this
  omega

/-- Too few octets left for the witness. -/
theorem mrAt_short (h : MrAt c ch a m L r k n) (hwb : witnessBytes c = L) (hL : 0 < L)
    (hav : ¬ L * (k + 1) + L ≤ r.length) : n = 0 ∧ primalityTest c (r.drop L) = none := by
  have e := mrLoop_step c ch a m L r (mrS c L r k).1 (mrS c L r k).2 (L * (k + 1)) h.go hwb hL
  rw [ite_f hav] at e
  have l1 : primalityTest c (r.drop L) = none := by rw [h.loop, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_none, itersOf] at this
  rw [Nat.div_eq_of_lt (by omega)] at this
  omega

/-- The start. -/
theorem mrAt_zero (hc : primalityTest c (r.drop L) = loop (mrStep c ch a m) (1, 0) (r.drop L)) (hwb : witnessBytes c = L)
    (hL : 0 < L) (hu : L ≤ r.length) :
    MrAt c ch a m L r 0 (itersOf L r.length (shapeOf (primalityTest c (r.drop L))) L - 1) := by
  have hg : goS ch (mrS c L r 0) := .inl (by simp [mrS, blindedChecks])
  refine ⟨by rw [hc]; simp [mrS], hg, ?_, by omega⟩
  have := (iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r) (i := 1) (uni := 0) (u := L) hg hwb hL
    (Nat.le_refl _) hu).2
  rw [← hc] at this
  rw [Nat.zero_add, Nat.mul_one]
  omega

end

end VG.Proof.RsaKeyGen
