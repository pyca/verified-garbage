module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Fixed-width encodings used by the DSA entry points -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem encodeBE_length (k value : Nat) : (Spec.Dsa.encodeBE k value).length = k := by
  rw [encodeBE_i2osp, VG.Proof.Rsa.i2osp_length]

theorem decodeBE_encodeBE {k value : Nat} (h : value < 256 ^ k) :
    Spec.Dsa.decodeBE (Spec.Dsa.encodeBE k value) = value := by
  rw [encodeBE_i2osp, decodeBE_os2ip, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt h]

theorem encodeBE_decodeBE (bytes : List Byte) : Spec.Dsa.encodeBE bytes.length (Spec.Dsa.decodeBE bytes) = bytes := by
  rw [encodeBE_i2osp, decodeBE_os2ip, VG.Proof.Rsa.i2osp_os2ip]

theorem decodeBE_lt (bytes : List Byte) : Spec.Dsa.decodeBE bytes < 256 ^ bytes.length :=
  VG.Proof.Rsa.lt_of_os2ip bytes

theorem encodeBE_eq_bytes {bytes : List Byte} {k value : Nat} (hlen : bytes.length = k)
    (hfit : value < 256 ^ k) : Spec.Dsa.encodeBE k value = bytes ↔ value = Spec.Dsa.decodeBE bytes := by
  constructor
  · intro h
    have hd := congrArg Spec.Dsa.decodeBE h
    rw [decodeBE_encodeBE hfit] at hd
    exact hd
  · intro h
    rw [h, ← hlen, encodeBE_decodeBE]

/-- The bytes (`Spec.Rsa.bytesAt`) of a memory that holds the list `L` at `lo`, for any `L`: the kernel compares
nothing byte by byte. To decide it for a witness's key, it read byte `i` of the list by walking
the `i` before it, for each of some four hundred bytes. -/
theorem bytesAt_of_list {L : List Byte} {lo n : Nat} {mem : Mem} (hn : L.length = n) (hfit : lo + n ≤ 2 ^ 64)
    (hm : ∀ a : Addr, lo ≤ a.toNat → a.toNat < lo + n → mem a = L[a.toNat - lo]?.getD 0) :
    (List.range n).map (fun i => mem (BitVec.ofNat 64 lo + BitVec.ofNat 64 i)) = L := by
  subst hn
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i h1 h2
    have e : (BitVec.ofNat 64 lo + BitVec.ofNat 64 i).toNat = lo + i := by
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega_using [hfit, h2])
    simp only [List.getElem_map, List.getElem_range]
    rw [hm _ (by rw [e]; omega_using []) (by rw [e]; omega_using [h2]), e, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem h2]
    rfl

end VG.Proof.Dsa
