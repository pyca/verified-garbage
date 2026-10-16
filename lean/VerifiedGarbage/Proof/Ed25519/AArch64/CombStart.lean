module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
public import VerifiedGarbage.Proof.Ed25519.CombDigits
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Where the AArch64 comb starts: `combStart` represents `[17 G]B`

For the comb's offset `G = combGVal`: the kernel compares `combStart` with `pointMul` of the
base point (`combStart_ok`, as `combG_ok`).
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

end VG.Proof.Ed25519.AArch64
