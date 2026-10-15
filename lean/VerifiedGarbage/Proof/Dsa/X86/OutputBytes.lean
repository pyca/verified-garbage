module

public import VerifiedGarbage.Proof.Dsa.PackedBytes

/-! # Joining the two encoded scalars into the packed signature result -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem bytesAt_split (mem : Mem) (ptr : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt mem ptr (a + b) =
      Spec.Rsa.bytesAt mem ptr a ++ Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 a) b := by
  unfold Spec.Rsa.bytesAt
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem signatureBytes {mem : Mem} {ptr : Addr} {len rv sv : Nat} (accepted : Prop) [Decidable accepted]
    (R : Spec.Rsa.bytesAt mem ptr len = if accepted then Spec.Dsa.encodeBE len rv else List.replicate len 0)
    (S : Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 len) len = if accepted then Spec.Dsa.encodeBE len sv else List.replicate len 0) :
    Spec.Rsa.bytesAt mem ptr (2 * len) =
      if accepted then Spec.Dsa.encodeBE len rv ++ Spec.Dsa.encodeBE len sv else List.replicate (2 * len) 0 := by
  rw [Nat.two_mul, bytesAt_split, R, S]
  by_cases H : accepted <;> simp only [H, ite_true, ite_false, List.replicate_append_replicate]

end VG.Proof.Dsa.X86
