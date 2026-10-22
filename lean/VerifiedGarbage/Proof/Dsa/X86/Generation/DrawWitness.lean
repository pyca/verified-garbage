module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets

/-! The copied suffix samples exactly the complete consumed RSA witness draw. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem draw_witness {s t : State} {base : Addr} {len drawBytes candidate : Nat} {src : BitVec 32}
    (length : len ≤ drawBytes) (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (copy : Spec.Rsa.bytesAt t.mem (off base Layout.witness) len =
      Spec.Rsa.bytesAt s.mem (off (byteAddr src) (drawBytes - len)) len) :
    Spec.RsaKeyGen.witness (candidate - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr src) drawBytes)) =
      Spec.RsaKeyGen.witness (candidate - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off base Layout.witness) len)) := by
  rw [copy]
  have append := VG.Proof.Dsa.Generation.bytesAt_append s.mem (byteAddr src) (drawBytes - len) len
  rw [Nat.sub_add_cancel length] at append
  rw [append]
  apply VG.Proof.Dsa.Generation.witness_drop_padding
  simpa only [VG.Proof.Bignum.bytesAt_length] using bits

end VG.Proof.Dsa.X86.Generation
