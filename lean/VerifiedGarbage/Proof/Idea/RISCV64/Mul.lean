module

import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Impl.Idea.RISCV64
public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run

/-!
# IDEA on RISC-V: ⊙ without branches

`mul_ok`: `mulCode` leaves `t0 ⊙ t1` (of their low 16 bits) in `t1`, with
the mask `0xffff` in `t2`, and changes nothing but `t0` and `t1`; the
arithmetic is the shared `prep_toNat` and `reduce`, as on PPC64LE.
`setMask_ok`: `setMask` puts the mask in `t2`.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-- A product of 64-bit values that does not wrap around. -/
theorem mul_ofNat (a b : BitVec 64) (_h : a.toNat * b.toNat < 2 ^ 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

theorem mul_ok (s : State) (h2 : s.gpr .t2 = 65535) :
    WP isa (.block mulCode) s fun t =>
      t.gpr .t1 = (Spec.Idea.mul ((s.gpr .t0).setWidth 16) ((s.gpr .t1).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem := by
  unfold mulCode
  crun [h2]
  have hA : ((s.gpr .t0 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .t0).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hB : ((s.gpr .t1 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .t1).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hp := Nat.mul_le_mul (residue_le ((s.gpr .t0).setWidth 16)) (residue_le ((s.gpr .t1).setWidth 16))
  rw [mul_ofNat _ _ (by rw [hA, hB]; exact Nat.lt_of_le_of_lt hp (by decide)), hA, hB, mul_toNat]
  exact reduce _ (Nat.le_trans hp (by decide)) 65535#64 rfl

theorem setMask_ok (s : State) :
    WP isa (.block setMask) s fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem := by
  unfold setMask
  crun
  decide

end VG.Proof.Idea.RISCV64
