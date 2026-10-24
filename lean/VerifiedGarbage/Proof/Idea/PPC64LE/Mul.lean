module

import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Impl.Idea.PPC64LE
public import VerifiedGarbage.Spec.Idea
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# IDEA on PPC64LE: ⊙ without branches

`mul_ok`: `mulCode` leaves `r11 ⊙ r12` (of their low 16 bits) in `r12`,
with the mask `0xffff` in `r0`, and changes nothing but `r11` and `r12`.
The arithmetic is the shared `prep_toNat` (the operands' residues) and
`reduce` (the product modulo 2¹⁶ + 1 from its halves, corrected by the sign
of their difference).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE

/-- A product of 64-bit values that does not wrap around. -/
theorem mul_ofNat (a b : BitVec 64) (_h : a.toNat * b.toNat < 2 ^ 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

theorem mul_ok (s : State) (h0 : s.gpr .r0 = 65535) :
    WP isa (.block mulCode) s fun t =>
      t.gpr .r12 = (Spec.Idea.mul ((s.gpr .r11).setWidth 16) ((s.gpr .r12).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem := by
  unfold mulCode
  crun [h0]
  have hA : ((s.gpr .r11 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .r11).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hB : ((s.gpr .r12 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .r12).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hp := Nat.mul_le_mul (residue_le ((s.gpr .r11).setWidth 16)) (residue_le ((s.gpr .r12).setWidth 16))
  rw [mul_ofNat _ _ (by rw [hA, hB]; exact Nat.lt_of_le_of_lt hp (by decide)), hA, hB, mul_toNat]
  exact reduce _ (Nat.le_trans hp (by decide)) 65535#64 rfl

end VG.Proof.Idea.PPC64LE
