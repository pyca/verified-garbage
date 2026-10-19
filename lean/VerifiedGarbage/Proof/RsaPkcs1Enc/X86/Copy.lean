module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.CopyBytes
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! # Byte-copy results as complete byte strings and exact memory frames -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem copyBytes_frame {s t : State} {src dst : BitVec 32} {n : Nat}
    (fit : dst.toNat + n ≤ 2 ^ 32) (h : CopyInv s src dst n n t) :
    Frame [⟨byteAddr dst, n⟩] s.mem t.mem := by
  intro x hx
  apply h.outside x
  intro i hi eq
  apply hx _ (List.mem_singleton_self _)
  rw [eq, byteAddr_add (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

theorem copyBytes_bytes {s t : State} {src dst : BitVec 32} {n : Nat}
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (h : CopyInv s src dst n n t) :
    Spec.Rsa.bytesAt t.mem (byteAddr dst) n = Spec.Rsa.bytesAt s.mem (byteAddr src) n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have byte := h.copied i bound
  rw [byteAddr_add (by omega), byteAddr_add (by omega)] at byte
  exact byte

end VG.Proof.RsaPkcs1Enc.X86.Dec
