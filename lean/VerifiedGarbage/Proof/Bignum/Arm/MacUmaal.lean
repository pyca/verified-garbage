module

public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! UMAAL returns exactly the diagonal product, accumulator and carry. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem macU_ok (s : State) :
    WP isa (.block macU) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.gpr .r1).toNat * (s.gpr .r2).toNat + (s.gpr .r10).toNat + (s.gpr .r11).toNat ∧
      MacFrame clobbers s t := by
  let v := (s.gpr .r1).toNat * (s.gpr .r2).toNat + (s.gpr .r11).toNat + (s.gpr .r10).toNat
  let t := (((s.setReg .r3 (s.gpr .r10)).setReg .r4 (s.gpr .r11)).setReg .r3
    (BitVec.ofNat 32 v)).setReg .r4 (BitVec.ofNat 32 (v / 2 ^ 32))
  refine WP.of_runBlock ⟨t, ?_, ?_, ?_⟩
  · simp only [macU, runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some,
      runBlock_nil, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rfl
  · change v % 2 ^ 32 + (v / 2 ^ 32) % 2 ^ 32 * 2 ^ 32 = _
    have bound := mac_bound (s.gpr .r1) (s.gpr .r2) (s.gpr .r10) (s.gpr .r11)
    have vb : v < 2 ^ 64 := by dsimp [v]; omega
    have hi : v / 2 ^ 32 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hi]
    dsimp [v]
    omega
  · refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro r hr
    have ne3 : r ≠ .r3 := by intro h; subst r; exact hr (by simp [clobbers])
    have ne4 : r ≠ .r4 := by intro h; subst r; exact hr (by simp [clobbers])
    simp only [t, gpr_setReg_of_ne _ _ ne4, gpr_setReg_of_ne _ _ ne3]

theorem macU_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block macU) := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Exec.block_iff] at h
  cases h
  rfl

end VG.Proof.Bignum.Arm
