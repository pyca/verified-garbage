module

public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets

/-! # Truncating an integer before I2OSP keeps the same output octets -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem i2osp_mod (x len : Nat) :
    Spec.Rsa.i2osp (x % 2 ^ (8 * len)) len = Spec.Rsa.i2osp x len := by
  have power : 2 ^ (8 * len) = 256 ^ len := by rw [Nat.pow_mul]
  rw [power, ← VG.Proof.Rsa.os2ip_i2osp]
  have H := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.i2osp x len)
  rw [VG.Proof.Rsa.i2osp_length] at H
  exact H

end VG.Proof.RsaKeyGen
