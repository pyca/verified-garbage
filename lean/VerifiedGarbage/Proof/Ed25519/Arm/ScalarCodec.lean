module
public import VerifiedGarbage.Proof.Ed25519.Arm.Packed
public import VerifiedGarbage.Spec.Ed25519.Contract

import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Impl.Ed25519.Arm.Word
import VerifiedGarbage.TCB.Arm.Isa

/-! Compact 16-bit limbs use the scalar specification's exact byte encoding. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem scalar_packed_decode (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) = packedV m p := by
  rw [decodeLE_eq]
  exact leNum_bytesAt2 m p 16

theorem scalar_packed_encode (m : Mem) (p : Addr) :
    Spec.Ed25519.bytesAt m p 32 = Spec.Ed25519.encodeLE 32 (packedV m p) := by
  have h := VG.Proof.X25519.bytesAt_leBytes m p 32
  rw [← VG.Proof.X25519.leNum_bytesAt_read, leNum_bytesAt2 m p 16] at h
  change Spec.Ed25519.bytesAt m p 32 = VG.Proof.X25519.leBytes 32 (packedV m p) at h
  rw [h]
  simp only [Spec.Ed25519.encodeLE, VG.Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

end VG.Proof.Ed25519.Arm
