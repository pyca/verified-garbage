module

public import VerifiedGarbage.Proof.MillerRabin.ExponentWords32

/-! # Extend a high-to-low modular prefix by one complete native word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64

theorem high_prefix_step (candidate k : Nat) :
    candidate / 2 ^ (32 * (k + 1)) * 2 ^ 32 + (VG.Proof.MillerRabin.exponentWord candidate k).toNat =
      candidate / 2 ^ (32 * k) := by
  rw [VG.Proof.MillerRabin.exponentWord, BitVec.toNat_ofNat,
    show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  have H := Nat.div_add_mod (candidate / 2 ^ (32 * k)) (2 ^ 32)
  omega

theorem high_mod_step (candidate exponent k : Nat) :
    ((candidate / 2 ^ (32 * (k + 1)) % exponent) * 2 ^ 32 +
      (VG.Proof.MillerRabin.exponentWord candidate k).toNat) % exponent =
      candidate / 2 ^ (32 * k) % exponent := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod, high_prefix_step]

end VG.Proof.RsaKeyGen.X86.Mod64
