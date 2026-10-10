import VerifiedGarbage.Impl.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.Bitsliced
import VerifiedGarbage.Proof.Sm4.Bitsliced32

/-! # The bits of the key schedule's constant planes -/

namespace VG.Proof.Sm4

open VG.Impl.Sm4 (planeOf fkWord planeOf32 fkLE)

theorem planeOf_bit (x : BitVec 32) (j : Nat) {p : Nat} (hp : p < 64) :
    (planeOf x j).getLsbD p = x.getLsbD (8 * (3 - p / 16) + j) := by
  rw [planeOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hp]
  simp [hp]

theorem planeOf_rel (x : BitVec 32) : WordRel (planeOf x) (fun _ => x) := fun b _ i hi j _ => by
  rw [planeOf_bit x j (by omega), show (16 * i + b) / 16 = i by omega]

theorem fkWord_bit {h t : Nat} (ht : t < 64) :
    (fkWord h).getLsbD t = (Spec.Sm4.fk.getD (2 * h + t / 32) 0).getLsbD (8 * (3 - t % 32 / 8) + t % 8) := by
  rw [fkWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range ht]
  simp [ht]

theorem planeOf32_bit (x : BitVec 32) (j : Nat) {p : Nat} (hp : p < 32) :
    (planeOf32 x j).getLsbD p = x.getLsbD (8 * (3 - p / 8) + j) := by
  rw [planeOf32, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hp]
  simp [hp]

theorem planeOf32_rel (x : BitVec 32) : W32.WordRel (planeOf32 x) (fun _ => x) := fun b _ i hi j _ => by
  rw [planeOf32_bit x j (by omega), show (8 * i + b) / 8 = i by omega]

theorem fkLE_bit {w t : Nat} (ht : t < 32) :
    (fkLE w).getLsbD t = (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - t / 8) + t % 8) := by
  rw [fkLE, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range ht]
  simp [ht]

end VG.Proof.Sm4
