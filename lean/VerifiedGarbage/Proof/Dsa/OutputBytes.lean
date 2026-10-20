module

public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-! # DSA's output bytes, on any target

A signature's bytes are the two encoded scalars (`signatureBytes`), and the
digest's prefix that DSA uses is a prefix of its bytes (`bytesAt_prefix`),
of at most 32 bytes for a supported domain (`shape_digest_width`).
-/

@[expose] public section
namespace VG.Proof.Dsa
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

theorem shape_digest_width {p q : Nat} (H : shapeValid p q) :
    Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) ∧ Spec.Dsa.bitLength q / 8 ≤ 32 := by
  have S := H.1
  unfold Spec.Dsa.supportedSizes at S
  omega

theorem bytesAt_prefix (mem : Mem) (ptr : Addr) (total count : Nat) :
    Spec.Rsa.bytesAt mem ptr (min total count) = (Spec.Rsa.bytesAt mem ptr total).take count := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_take, List.length_map, List.length_range]
    omega
  · intro i hi hj
    simp only [List.getElem_take, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

end VG.Proof.Dsa
