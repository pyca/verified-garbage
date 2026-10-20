module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Byte reversal implements RSA's OS2IP -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont

/-- The complete loop computes the integer of the original big-endian input. -/
theorem ReverseInv.os2ip {s0 s : State} {src dst : BitVec 32} {n : Nat}
    (inv : ReverseInv s0 (src + BitVec.ofNat 32 (n - 1)) dst n n s)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32) :
    (s.mem.read (byteAddr dst) n).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (byteAddr src) n) := by
  apply reversed_read
  intro j hj
  have h := inv.copied j hj
  rw [byteAddr_add (by omega), reverse_source_addr src srcFit hj] at h
  exact h

end VG.Proof.Bignum.X86
