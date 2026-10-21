module

public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # Cached R² converts any sampled witness to Montgomery form -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.MillerRabin

theorem witness_r2 {c w x : Nat} (odd : c % 2 = 1) :
    Word32.mm c w x (2 ^ (64 * w) * 2 ^ (64 * w) % c) = x * 2 ^ (64 * w) % c := by
  have cancel : (2 ^ (64 * w) * 2 ^ (64 * w) % c) * Word32.rinv c w % c = 2 ^ (64 * w) % c := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Word32.R_rinv odd,
      ← Nat.mul_mod, Nat.mul_one]
  unfold Word32.mm
  rw [Nat.mul_assoc, Nat.mul_mod, cancel, ← Nat.mul_mod]

end VG.Proof.RsaKeyGen
