module

public import VerifiedGarbage.Spec.Rsa.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The masked public-operation result is exactly the shared checked-RSA postcondition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG

theorem publicOutput_written {mem : Mem} {dst : Addr} {k : Nat} {nb eb xb : List Byte} {r : BitVec 32}
    (length : nb.length = k) (modulus : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (exponent : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true)
    (bytes : Spec.Rsa.bytesAt mem dst k =
      (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
        Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip nb)) k
       else List.replicate k 0))
    (status : r = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat) :
    Spec.Rsa.written mem dst k r (Spec.Rsa.publicOpChecked nb eb xb) := by
  by_cases valid : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb
  · simpa [Spec.Rsa.publicOpChecked, exponent, Spec.Rsa.publicOp, length, modulus,
      Spec.Rsa.encrypt, valid, Spec.Rsa.written] using And.intro status bytes
  · simpa [Spec.Rsa.publicOpChecked, exponent, Spec.Rsa.publicOp, length, modulus,
      Spec.Rsa.encrypt, valid, Spec.Rsa.written] using And.intro status bytes

end VG.Proof.Bignum.Arm
