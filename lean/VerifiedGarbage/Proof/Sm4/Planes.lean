import VerifiedGarbage.Impl.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.Bitsliced

/-! # The bits of the key schedule's constant planes -/

namespace VG.Proof.Sm4

open VG.Impl.Sm4 (planeOf fkWord)

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

/-- Plane `j` of `x` from four masks, one per byte: what `planeOf` computes,
in a form the kernel evaluates quickly (`planeOf_eq_masks`). -/
def planeMasks (x : BitVec 32) (j : Nat) : BitVec 64 :=
  (bif x.getLsbD (24 + j) then 0xFFFF#64 else 0) ||| (bif x.getLsbD (16 + j) then 0xFFFF0000#64 else 0) |||
    (bif x.getLsbD (8 + j) then 0xFFFF00000000#64 else 0) ||| (bif x.getLsbD j then 0xFFFF000000000000#64 else 0)

private theorem masks_bit : ∀ a b c d : Bool, ∀ p < 64,
    ((bif a then 0xFFFF#64 else 0) ||| (bif b then 0xFFFF0000#64 else 0) |||
      (bif c then 0xFFFF00000000#64 else 0) ||| (bif d then 0xFFFF000000000000#64 else 0)).getLsbD p =
      if p / 16 = 0 then a else if p / 16 = 1 then b else if p / 16 = 2 then c else d := by
  decide +kernel

theorem planeOf_eq_masks (x : BitVec 32) (j : Nat) : planeOf x j = planeMasks x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [planeOf_bit x j hp, planeMasks, masks_bit _ _ _ _ p hp]
  rcases (by omega : p / 16 = 0 ∨ p / 16 = 1 ∨ p / 16 = 2 ∨ p / 16 = 3) with h | h | h | h <;>
    simp only [h, ↓reduceIte, Nat.reduceSub, Nat.reduceMul, Nat.reduceEqDiff, Nat.add_comm, Nat.add_zero]

end VG.Proof.Sm4
