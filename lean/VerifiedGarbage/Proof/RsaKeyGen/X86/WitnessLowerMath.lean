module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.KeyBits32

/-! # A witness is below two exactly when its high words and cleared low word are zero -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.Proof.Mont

theorem clear_low_zero (x : BitVec 32) :
    (x ||| 1#32) ^^^ 1#32 = 0#32 ↔ x.toNat < 2 := by
  rw [← BitVec.toNat_inj]
  change ((x ||| (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 0 ↔ x.toNat < 2
  rw [VG.Proof.Rsa.KeyBits32.bv_clr_one]
  change 2 * (x.toNat / 2) = 0 ↔ x.toNat < 2
  omega

theorem below_two (m : Mem) (base : Addr) (src n : Nat) (positive : 0 < n) :
    val32 m base src n < 2 ↔
      val32 m base (src + 4) (n - 1) = 0 ∧ (m.readW (off base src) 32).toNat < 2 := by
  rw [show n = n - 1 + 1 by omega, val32, show n - 1 + 1 - 1 = n - 1 by omega]
  change w32 m base src + 2 ^ 32 * val32 m base (src + 4) (n - 1) < 2 ↔
    val32 m base (src + 4) (n - 1) = 0 ∧ w32 m base src < 2
  omega

end VG.Proof.RsaKeyGen.X86.WitnessLower
