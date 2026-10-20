module
public import VerifiedGarbage.Proof.Divstep.PackedDef

import VerifiedGarbage.Proof.Divstep.Packed
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Packed divsteps: the `g` row's low bits

Before each step of a chunk, the `g` row's bits below the step's are zero
(`psteps_shl`), so code may test the step's parity by its bit alone.
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- Before step `k < n` of `psteps_rel`, the `g` row shifted left by `63 - k`
is `0` or `2^63`: its bits below `k` are zero. -/
theorem psteps_shl {d f g P Q : Int} {n : Nat} (hn : n ≤ 62) (hf : f % 2 = 1) (hd : |d| + 2 * n < 2 ^ 62)
    (hP : P % 2 ^ n = f % 2 ^ n) (hQ : Q % 2 ^ n = g % 2 ^ n) {k : Nat} (hk : k < n) :
    ((psteps k (~~~BitVec.ofInt 64 d, BitVec.ofInt 64 P, BitVec.ofInt 64 Q)).2.2 <<< (63 - k)).toNat = 0 ∨
      ((psteps k (~~~BitVec.ofInt 64 d, BitVec.ofInt 64 P, BitVec.ofInt 64 Q)).2.2 <<< (63 - k)).toNat =
        2 ^ 63 := by
  rw [psteps_rel hn hf hd hP hQ k hk.le]
  have hb := Int.emod_two_eq_zero_or_one (msteps k (MSt.init d f g)).g
  have hG : ((msteps k (MSt.init d f g)).q * P + (msteps k (MSt.init d f g)).r * Q) % 2 ^ (k + 1) =
      2 ^ k * ((msteps k (MSt.init d f g)).g % 2) := by
    obtain ⟨-, mg⟩ := msteps_mat (d := d) (g := g) hf k
    have hdv : (2 : Int) ^ (k + 1) ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    rw [← pow_mul_emod_succ, mg, ← Int.emod_emod_of_dvd _ hdv, ← Int.emod_emod_of_dvd (_ * f + _) hdv]
    congr 1
    rw [Int.add_emod, Int.mul_emod _ P, hP, ← Int.mul_emod, Int.mul_emod _ Q, hQ, ← Int.mul_emod, ← Int.add_emod]
  have hs := shl_bit (by omega) hb hG
  simp only at hs ⊢
  rcases hb with h | h <;> rw [h] at hs
  · left; simpa using hs
  · right; simpa using hs

end VG.Proof.Divstep
