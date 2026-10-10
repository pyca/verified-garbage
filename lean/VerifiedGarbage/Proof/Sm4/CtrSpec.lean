import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.AesCtr.Counter
import VerifiedGarbage.Spec.Sm4.Ctr

/-!
# SM4-CTR's result, on every target

`ctr_of_dinv`: when the data loop has replaced each block `j` with its XOR
with SM4's encryption of the counter block `T₁ + j` (`ctrBlock`), the blocks
are `Spec.Ctr.crypt`'s. Nothing here depends on a target.
-/

namespace VG.Proof.Sm4

open VG VG.Spec.Sm4
open VG.Spec.Ctr (ofNat toNat)

/-- The counter block `V` (its 16 big-endian bytes), as an SM4 block. -/
def ctrBlock (V : Nat) : Block := Vector.ofFn fun i => (ofNat V 16).getD i.val 0

theorem bytesAt_eq_blockAt (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 = (blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 h2
  simp [Spec.Aes.bytesAt, blockAt]

theorem xor_toList (a b : Block) :
    (Vector.ofFn fun i : Fin 16 => a.getD i.val 0 ^^^ b.getD i.val 0).toList = Spec.Cbc.xor b.toList a.toList := by
  apply List.ext_getElem (by simp [Spec.Cbc.xor])
  intro i h1 h2
  have hi : i < 16 := by simpa using h1
  simp only [Spec.Cbc.xor, List.getElem_zipWith, Vector.getElem_toList, Vector.getElem_ofFn]
  rw [BitVec.xor_comm]
  simp [Vector.getD, Array.getD, hi]

/-- The data blocks after the data loop, as CTR's. -/
theorem ctr_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Block} (sch : Schedule) {t : List Byte}
    (ht : t.length = 16) (hF : ∀ j < n, F j = Vector.ofFn fun i : Fin 16 =>
      (encryptBlock sch (ctrBlock (toNat t + j))).getD i.val 0 ^^^
        (blockAt m₀ (D + BitVec.ofNat 64 (16 * j))).getD i.val 0)
    (h : DInv m₀ m D n n F) :
    Spec.Cbc.blocksAt m D n = Spec.Ctr.crypt (cipher sch) t (Spec.Cbc.blocksAt m₀ D n) := by
  have hb := blocksAt_of_dinv h
  have hl : (Spec.Cbc.blocksAt m₀ D n).length = n := by simp [Spec.Cbc.blocksAt]
  have hL : Spec.Cbc.blocksAt m D n = (blocksAt m D n).map Vector.toList := by
    simp only [Spec.Cbc.blocksAt, blocksAt, List.map_map]
    exact List.map_congr_left fun j _ => bytesAt_eq_blockAt m _
  rw [hL, hb, Spec.Ctr.crypt, hl, AesCtr.counters_eq_map, Spec.Cbc.blocksAt, List.map_map, List.map_map,
    List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [hF j hj, AesCtr.next_eq ht, bytesAt_eq_blockAt, xor_toList]
  rfl

end VG.Proof.Sm4
