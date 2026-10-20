module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
public import VerifiedGarbage.Proof.Ed25519.CombDigits

/-!
# Where the AArch64 comb starts: `combStart` represents `[17 G]B`

For the comb's offset `G = combGVal`: the kernel compares `combStart` with `pointMul` of the
base point (`combStart_ok`, as `combG_ok`), and `combStart8` with `[17 G - 8]B`, where the comb
of a scalar with bits 0–2 clear starts for bit 3 clear (`combStart8_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG.Spec.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

private def combStartCheck (p : Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check : combStartCheck (pointMul (17 * combGVal) basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * combGVal) • baseAff) := by
  have hp := pointMul_rep (17 * combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStartAff) hp hx hy

private def combStart8Check (p : Point) : Bool :=
  combStart8.X * p.Z == p.X && combStart8.Y * p.Z == p.Y && p.Z != 0

private theorem combStart8_check :
    combStart8Check (pointMul (17 * combGVal - 8) basePoint) = true := by
  decide +kernel

theorem combStart8_ok : Rep combStart8 ((17 * combGVal - 8) • baseAff) := by
  have hp := pointMul_rep (17 * combGVal - 8) basePoint_rep
  have hc := combStart8_check
  simp only [combStart8Check, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStart8Aff) hp hx hy

end VG.Proof.Ed25519.AArch64
