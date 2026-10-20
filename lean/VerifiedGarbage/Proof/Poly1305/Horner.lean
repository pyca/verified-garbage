module

public import VerifiedGarbage.Proof.Poly1305.Spec

/-!
# Poly1305: Horner's rule in four lanes

A vector implementation can absorb four blocks at a time in four lanes: lane
`k` holds `V_k`, and a group of blocks `m₀ … m₃` makes it `(V_k + m_k) r⁴`; at
the end, the last group makes it `(V_k + m_k) r^(4-k)` and the lanes are
summed. With `S = r⁴ V₀ + r³ V₁ + r² V₂ + r V₃`, the invariant is `S ≡ r⁴ a`
for the accumulator `a` of the blocks so far (starting with `V₀ = a`, the
others 0).

The congruences are stated as equal residues, `x % P = y % P` (what
`Nat.ModEq P x y` unfolds to), and proven with core lemmas and `grind`, so
that the many modules that import this one (through the vector
implementations, and the ChaCha20-Poly1305 proofs that call them) do not
import Mathlib's algebra.
-/

@[expose] public section

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

/-- The value of a block with its `0x01` byte appended. -/
abbrev mv (b : List Byte) : Nat := leNum (b ++ [0x01])

/-- Sums of numbers with equal residues have equal residues. -/
theorem add_mod_congr {a a' b b' : Nat} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a + b) % P = (a' + b') % P := by
  rw [Nat.add_mod, ha, hb, ← Nat.add_mod]

/-- So do multiples of numbers with equal residues. -/
theorem mul_mod_congr (c : Nat) {a a' : Nat} (ha : a % P = a' % P) : (c * a) % P = (c * a') % P := by
  rw [Nat.mul_mod, ha, ← Nat.mul_mod]

theorem mod_step {x y : Nat} (r v : Nat) (h : x % P = y % P) : r * (x + v) % P % P = r * (y + v) % P := by
  rw [Nat.mod_mod]; exact mul_mod_congr r (add_mod_congr h rfl)

theorem absorbAll_four {r a : Nat} {b0 b1 b2 b3 : List Byte} (h0 : b0.length = 16) (h1 : b1.length = 16)
    (h2 : b2.length = 16) (h3 : b3.length = 16) :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3) % P =
      (r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) % P := by
  have l0 : (b0 ++ b1).length % 16 = 0 := by simp [h0, h1]
  have l1 : (b0 ++ b1 ++ b2).length % 16 = 0 := by simp [h0, h1, h2]
  rw [absorbAll_append l1, absorbAll_append l0, absorbAll_append (by omega),
    absorbAll_block (by omega) (by omega), absorbAll_block (by omega) (by omega),
    absorbAll_block (by omega) (by omega), absorbAll_block (by omega) (by omega)]
  refine (mod_step r _ (mod_step r _ (mod_step r _ (Nat.mod_mod _ _)))).trans ?_
  rw [show r * (r * (r * (r * (a + mv b0) + mv b1) + mv b2) + mv b3) =
    r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3 by grind]

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes (r V0 V1 V2 V3 : Nat) : Nat := r ^ 4 * V0 + r ^ 3 * V1 + r ^ 2 * V2 + r * V3

section
variable {r X V0 V1 V2 V3 W0 W1 W2 W3 : Nat} {b0 b1 b2 b3 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (hS : lanes r V0 V1 V2 V3 % P = r ^ 4 * X % P)
include h0 h1 h2 h3 hS

/-- A group of four blocks, each lane multiplied by `r⁴`. -/
theorem horner_step (e0 : W0 % P = (V0 + mv b0) * r ^ 4 % P) (e1 : W1 % P = (V1 + mv b1) * r ^ 4 % P)
    (e2 : W2 % P = (V2 + mv b2) * r ^ 4 % P) (e3 : W3 % P = (V3 + mv b3) * r ^ 4 % P) :
    lanes r W0 W1 W2 W3 % P = r ^ 4 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) % P := by
  have hA := mul_mod_congr (r ^ 4) (absorbAll_four (r := r) (a := X) h0 h1 h2 h3)
  have hL : lanes r W0 W1 W2 W3 % P = r ^ 4 * (lanes r V0 V1 V2 V3 +
      (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)) % P := by
    refine (add_mod_congr (add_mod_congr (add_mod_congr (mul_mod_congr _ e0) (mul_mod_congr _ e1))
      (mul_mod_congr _ e2)) (mul_mod_congr _ e3)).trans ?_
    rw [show r ^ 4 * ((V0 + mv b0) * r ^ 4) + r ^ 3 * ((V1 + mv b1) * r ^ 4) +
        r ^ 2 * ((V2 + mv b2) * r ^ 4) + r * ((V3 + mv b3) * r ^ 4) =
        r ^ 4 * (lanes r V0 V1 V2 V3 + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)) by
      simp only [lanes]; grind]
  rw [hL, mul_mod_congr _ (add_mod_congr hS rfl), hA]
  congr 1
  grind

/-- The last group, lane `k` multiplied by `r^(4-k)`, and the lanes summed. -/
theorem horner_last (e0 : W0 % P = (V0 + mv b0) * r ^ 4 % P) (e1 : W1 % P = (V1 + mv b1) * r ^ 3 % P)
    (e2 : W2 % P = (V2 + mv b2) * r ^ 2 % P) (e3 : W3 % P = (V3 + mv b3) * r % P) :
    (W0 + W1 + W2 + W3) % P = absorbAll r X (b0 ++ b1 ++ b2 ++ b3) % P := by
  have hA := absorbAll_four (r := r) (a := X) h0 h1 h2 h3
  refine (add_mod_congr (add_mod_congr (add_mod_congr e0 e1) e2) e3).trans ?_
  rw [show (V0 + mv b0) * r ^ 4 + (V1 + mv b1) * r ^ 3 + (V2 + mv b2) * r ^ 2 + (V3 + mv b3) * r =
    lanes r V0 V1 V2 V3 + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) by
      simp only [lanes]; grind, add_mod_congr hS rfl, hA]
  congr 1
  grind

end

end VG.Proof.Poly1305
