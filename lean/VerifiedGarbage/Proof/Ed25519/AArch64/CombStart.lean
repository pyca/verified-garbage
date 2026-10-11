import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
import VerifiedGarbage.Proof.Ed25519.CombDigits

/-!
# Where the AArch64 comb starts: `combStart` represents `[G']B`

`G' = 17 G / 16` modulo the group's order, for the comb's offset `G =
combGVal`: the kernel compares `combStart` with `pointMul` of the base point
(`combStart_ok`, as `combG_ok`), and `[16 G']B` with `[17 G]B` projectively
(`combStart_16`), so the four doublings of `[G']B` give `[17 G]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG.Spec.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- `G' = 17 G / 16` modulo the group's order. -/
def combStartVal : Nat := 241233519244408740465772885434766474680441309164731664980943997787710529170

private def combStartCheck (p : Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check : combStartCheck (pointMul combStartVal basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart (combStartVal • baseAff) := by
  have hp := pointMul_rep combStartVal basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  refine hp.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ ?_
  · show toZ combStart.X * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ combStart.Y * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]
  · show toZ (combStartAff.1 * combStartAff.2) * toZ 1 = toZ combStartAff.1 * toZ combStartAff.2
    rw [toZ_mul, toZ_one, mul_one]

private theorem combStart_16_check :
    pointEqual (pointMul (16 * combStartVal) basePoint) (pointMul (17 * combGVal) basePoint) = true := by
  decide +kernel

/-- Four doublings of `[G']B` give `[17 G]B`: `16 G' ≡ 17 G` modulo the group's order. -/
theorem combStart_16 : (16 * combStartVal) • baseAff = (17 * combGVal) • baseAff := by
  have hp := pointMul_rep (16 * combStartVal) basePoint_rep
  have hq := pointMul_rep (17 * combGVal) basePoint_rep
  have h := combStart_16_check
  simp only [pointEqual, Bool.and_eq_true, beq_iff_eq] at h
  have e1 := congrArg toZ h.1
  have e2 := congrArg toZ h.2
  rw [toZ_mul, toZ_mul, hp.x, hq.x] at e1
  rw [toZ_mul, toZ_mul, hp.y, hq.y] at e2
  have hz := mul_ne_zero hp.z hq.z
  ext
  · exact mul_right_cancel₀ hz (by rw [← mul_assoc, e1, mul_assoc]; exact congrArg _ (mul_comm _ _))
  · exact mul_right_cancel₀ hz (by rw [← mul_assoc, e2, mul_assoc]; exact congrArg _ (mul_comm _ _))

end VG.Proof.Ed25519.AArch64
