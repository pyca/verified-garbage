module

public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM: memory satisfying the precondition of `vg_mlkem*_encaps_h`

`encapsHContract`'s precondition asks that the 32 bytes at `h` be `H(ek)`:
`hMem n` holds `H` of `n` zero bytes at `0x2000`, and zero elsewhere, so
the `n` bytes at `0x1000`, an encapsulation key, are zero and those at
`0x2000` are their hash (`hMem_h`). Each target's witness of the
precondition is a state with this memory.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `n` zero bytes. -/
def zeroBytes (n : Nat) : List Byte := bytesAt (fun _ => 0) 0x1000 n

/-- `H` of `n` zero bytes at `0x2000`, and zero elsewhere. -/
def hMem (n : Nat) : Mem := fun a =>
  if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2020 then (H (zeroBytes n)).getD (a.toNat - 0x2000) 0 else 0

theorem hMem_h {n : Nat} (hk : n ≤ 0x1000) : bytesAt (hMem n) 0x2000 32 = H (bytesAt (hMem n) 0x1000 n) := by
  have ek : bytesAt (hMem n) 0x1000 n = zeroBytes n := by
    simp only [zeroBytes, bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    simp only [hMem]
    rw [ite_eq_right_iff.mpr fun h => absurd h ?_]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4096 : BitVec 64).toNat = 4096 from rfl]
    omega
  rw [ek]
  refine List.ext_getElem (by rw [H_length]; simp [bytesAt]) fun i h₁ h₂ => ?_
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, hMem]
  have e : (0x2000 + BitVec.ofNat 64 i : BitVec 64).toNat = 0x2000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8192 : BitVec 64).toNat = 8192 from rfl]; omega
  simp only [e]
  split
  · rw [Nat.add_sub_cancel_left]; simp [List.getD_eq_getElem?_getD, h₂]
  · omega

end VG.Proof.MlKem
