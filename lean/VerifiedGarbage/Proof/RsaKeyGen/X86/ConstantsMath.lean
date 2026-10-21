module

public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # Multiplying a plain one by R² produces the Montgomery representation of one -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.Proof.MillerRabin

theorem one_r2 {c w : Nat} (odd : c % 2 = 1) :
    Word32.mm c w 1 (2 ^ (64 * w) * 2 ^ (64 * w) % c) = 2 ^ (64 * w) % c := by
  unfold Word32.mm
  rw [Nat.one_mul, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Word32.R_rinv odd,
    ← Nat.mul_mod, Nat.mul_one]

end VG.Proof.RsaKeyGen.X86.Constants
