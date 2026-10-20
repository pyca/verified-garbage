module

public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! Reconstruct the exact scalar encoding from the prefix, masked byte, and suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Proof.Mont

theorem keyCutEncoding {m : Mem} {dst : Addr} {rb : List Byte} {ld : Nat} {mask : Byte}
    (bound : ld < rb.length)
    (prefixBytes : Spec.Rsa.bytesAt m dst ld = List.replicate ld 0)
    (firstByte : m (off dst ld) = rb.getD ld 0 &&& mask)
    (suffixBytes : Spec.Rsa.bytesAt m (off dst (ld + 1)) (rb.length - (ld + 1)) = rb.drop (ld + 1)) :
    Spec.Rsa.bytesAt m dst rb.length = VG.Proof.Ffdh.KeyScalar.cut rb ld mask := by
  have splitLength : rb.length = ld + (1 + (rb.length - (ld + 1))) := by omega
  rw [splitLength, VG.Proof.Dsa.Generation.bytesAt_append,
    VG.Proof.Dsa.Generation.bytesAt_append, prefixBytes]
  have one : Spec.Rsa.bytesAt m (off dst ld) 1 = [rb.getD ld 0 &&& mask] := by
    simpa only [Spec.Rsa.bytesAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, BitVec.add_zero, List.nil_append] using congrArg (fun b : Byte => [b]) firstByte
  rw [one]
  have ptr : off (off dst ld) 1 = off dst (ld + 1) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  change List.replicate ld 0 ++ ([rb.getD ld 0 &&& mask] ++
    Spec.Rsa.bytesAt m (off (off dst ld) 1) (rb.length - (ld + 1))) = _
  rw [ptr, suffixBytes]
  rfl

end VG.Proof.Ffdh.Arm
