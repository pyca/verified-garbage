module

public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets

/-! A fixed-width big-endian encoding is determined by its integer value. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG

theorem bytesAt_eq_of_value {m : Mem} {base : Addr} {n : Nat} {xs : List Byte}
    (length : xs.length = n)
    (value : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m base n) = Spec.Rsa.os2ip xs) :
    Spec.Rsa.bytesAt m base n = xs := by
  have encoded := (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt m base n)).symm
  rw [bytesAt_length, value, ← length] at encoded
  simpa only [length] using encoded.trans (VG.Proof.Rsa.i2osp_os2ip xs)

end VG.Proof.Bignum
