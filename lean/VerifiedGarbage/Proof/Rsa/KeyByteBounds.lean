module

import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa

/-! # A factor shorter than the modulus leaves room for modular addition -/

@[expose] public section
namespace VG.Proof.Rsa
open VG

theorem short_factor_bounds {bs : List Byte} {k w : Nat} (short : bs.length < k) (fits : k ≤ 4 * w) :
    Spec.Rsa.os2ip bs < 256 ^ (k - 1) ∧
    2 * Spec.Rsa.os2ip bs ≤ 2 ^ (32 * w) ∧ Spec.Rsa.os2ip bs < 2 ^ (32 * w) := by
  have value := lt_of_os2ip bs
  have small : 256 ^ bs.length ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have room : 2 * 256 ^ bs.length ≤ 2 ^ (32 * w) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨Nat.lt_of_lt_of_le value small, by omega, by omega⟩
end VG.Proof.Rsa
