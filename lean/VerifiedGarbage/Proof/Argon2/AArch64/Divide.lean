module

public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Facts shared by Argon2's fixed-time division and remainder -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

theorem prefix_step (x : BitVec 64) (j : Nat) :
    x.toNat / 2 ^ j = 2 * (x.toNat / 2 ^ (j + 1)) + (x.getLsbD j).toNat := by
  have h := Nat.mod_add_div (x.toNat / 2 ^ j) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  simp only [← BitVec.testBit_toNat, Nat.toNat_testBit]
  omega

def changed : List Reg := [.x3, .x4, .x6, .x8, .x5, .x9]

end VG.Proof.Argon2.AArch64.Divide
