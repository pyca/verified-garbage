module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Component slices of packed big-endian DSA keys and signatures -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem bytesAt_slice (mem : Mem) (ptr : Addr) {total offset len : Nat} (h : offset + len ≤ total) :
    ((Spec.Rsa.bytesAt mem ptr total).drop offset).take len =
      Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 offset) len := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    omega
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_drop, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem publicKeyBytes_at (mem : Mem) (ptr : Addr) {pLen qLen total : Nat}
    (h : 3 * pLen + qLen ≤ total) :
    Spec.Dsa.publicKeyBytes pLen qLen (Spec.Rsa.bytesAt mem ptr total) =
      ⟨⟨Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem ptr pLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 pLen) qLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 (pLen + qLen)) pLen)⟩,
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 (2 * pLen + qLen)) pLen), none⟩ := by
  have h0 := bytesAt_slice mem ptr (offset := 0) (len := pLen) (by omega : 0 + pLen ≤ total)
  simp only [List.drop_zero, BitVec.add_zero] at h0
  simp only [Spec.Dsa.publicKeyBytes, h0,
    bytesAt_slice mem ptr (by omega : pLen + qLen ≤ total),
    bytesAt_slice mem ptr (by omega : (pLen + qLen) + pLen ≤ total),
    bytesAt_slice mem ptr (by omega : (2 * pLen + qLen) + pLen ≤ total)]

theorem privateKeyBytes_at (mem : Mem) (ptr : Addr) {pLen qLen total : Nat}
    (h : 3 * pLen + 2 * qLen ≤ total) :
    Spec.Dsa.privateKeyBytes pLen qLen (Spec.Rsa.bytesAt mem ptr total) =
      { Spec.Dsa.publicKeyBytes pLen qLen (Spec.Rsa.bytesAt mem ptr total) with
        x := some (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 (3 * pLen + qLen)) qLen)) } := by
  simp only [Spec.Dsa.privateKeyBytes, bytesAt_slice mem ptr (by omega : (3 * pLen + qLen) + qLen ≤ total)]

end VG.Proof.Dsa
