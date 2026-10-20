module

public import VerifiedGarbage.Impl.Bignum.Arm.Csub
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Rewind the two sources and restore the selection loop's public count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem selectPrepare_ok (s : State) :
    WP isa (.block selectPrepare) s fun t =>
      t.gpr .r0 = s.gpr .r9 ∧ t.gpr .r10 = s.gpr .r0 - (s.gpr .r7 <<< 2) ∧
      t.gpr .r12 = s.gpr .r10 - (s.gpr .r7 <<< 2) ∧ t.gpr .lr = s.gpr .r7 ∧
      Preserves [.r0, .r10, .r12, .lr] s t := by
  apply WP.of_runBlock
  simp only [selectPrepare, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem rewind32 (base : BitVec 32) (o n : Nat) :
    base + BitVec.ofNat 32 (o + 4 * n) - (BitVec.ofNat 32 n <<< 2) =
      base + BitVec.ofNat 32 o := by
  have scaled : BitVec.ofNat 32 n <<< 2 = BitVec.ofNat 32 (4 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_mul_mod, Nat.mul_comm n]
  rw [scaled, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]

end VG.Proof.Bignum.Arm
