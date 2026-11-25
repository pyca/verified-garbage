module

public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

/-! # Halfword lanes of AArch64 vectors -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64

theorem getLsbD_vhalf (x : BitVec 128) (e : Nat) {j : Nat} (hj : j < 16) :
    (vhalf x e).getLsbD j = x.getLsbD (16 * e + j) := by
  simp only [vhalf, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]

theorem vhalf_ofVHalves (f : Nat → BitVec 16) {e : Nat} (he : e < 8) : vhalf (ofVHalves f) e = f e := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_vhalf _ _ hj]
  simp only [ofVHalves, getLsbD_append_block _ _ _ hj]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]
  | _ + 8, h => exact absurd h (by omega_using [])

/-- Two vectors with the same halfwords are the same. -/
theorem vhalf_ext {x y : BitVec 128} (h : ∀ e < 8, vhalf x e = vhalf y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun w : BitVec 16 => w.getLsbD (i % 16)) (h (i / 16) (by omega_using [hi]))
  rwa [getLsbD_vhalf _ _ (by omega_using []), getLsbD_vhalf _ _ (by omega_using []),
    show 16 * (i / 16) + i % 16 = i by omega_using []] at this

theorem vhalf_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 8) : vhalf (VArr.h8.map2 f x y) e = f 16 (vhalf x e) (vhalf y e) := by
  simp only [VArr.map2]; rw [vhalf_ofVHalves _ he]

theorem vhalf_and (x y : BitVec 128) (e : Nat) : vhalf (x &&& y) e = vhalf x e &&& vhalf y e := by
  simp only [vhalf, BitVec.extractLsb'_and]

/-- A halfword of a word. -/
theorem vhalf_vword (x : BitVec 128) (e : Nat) :
    vhalf x e = (vword x (e / 2)).extractLsb' (16 * (e % 2)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_vhalf _ _ hj]
  simp only [vword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
    decide_eq_true (show 16 * (e % 2) + j < 32 by omega_using [hj])]
  exact congrArg _ (by omega_using [])

theorem vword_lo (x : BitVec 128) (j : Nat) : BitVec.extractLsb' 0 16 (vword x j) = vhalf x (2 * j) := by
  rw [vhalf_vword, show 2 * j / 2 = j by omega_using [], show 2 * j % 2 = 0 by omega_using []]

theorem vword_halves (x : BitVec 128) (k : Nat) : vword x k = vhalf x (2 * k + 1) ++ vhalf x (2 * k) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 16
  · simp only [h, ↓reduceIte, getLsbD_vhalf _ _ h]
    simp only [vword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega_using [])
  · simp only [h, ↓reduceIte, getLsbD_vhalf _ _ (show j - 16 < 16 by omega_using [hj])]
    simp only [vword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega_using [h])

theorem h8_lanes_getD (x : BitVec 128) {i : Nat} (hi : i < 8) :
    (VArr.h8.lanes x).getD i 0 = (vhalf x i).setWidth 128 := by
  simp only [VArr.lanes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem setWidth_setWidth16 (x : BitVec 16) : (x.setWidth 128).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (a := x.toNat) (by have := x.isLt; omega_using [this]),
    Nat.mod_eq_of_lt x.isLt]

/-- The halfwords of a permutation of halfwords. -/
theorem vhalf_perm_h8 (op : VPermOp) (x y : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (op.eval VArr.h8 x y) e =
      match op with
      | VPermOp.zip1 => if e % 2 = 0 then vhalf x (e / 2) else vhalf y (e / 2)
      | VPermOp.zip2 => if e % 2 = 0 then vhalf x (4 + e / 2) else vhalf y (4 + e / 2)
      | VPermOp.trn1 => if e % 2 = 0 then vhalf x e else vhalf y (e - 1)
      | VPermOp.trn2 => if e % 2 = 0 then vhalf x (e + 1) else vhalf y e
      | VPermOp.uzp1 => if e < 4 then vhalf x (2 * e) else vhalf y (2 * e - 8)
      | VPermOp.uzp2 => if e < 4 then vhalf x (2 * e + 1) else vhalf y (2 * e - 7) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vhalf_ofVHalves _ he, show (VArr.h8.lanes x).length = 8 from rfl]
  have hl (z : BitVec 128) {i : Nat} (hi : i < 8) : ((VArr.h8.lanes z).getD i 0).setWidth 16 = vhalf z i := by
    rw [h8_lanes_getD _ hi, setWidth_setWidth16]
  have hu {i : Nat} (hi : i < 16) : ((VArr.h8.lanes x ++ VArr.h8.lanes y).getD i 0).setWidth 16 =
      if i < 8 then vhalf x i else vhalf y (i - 8) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append, show (VArr.h8.lanes x).length = 8 from rfl]
    by_cases h : i < 8
    · rw [ite_eq_left h, ite_eq_left h, ← List.getD_eq_getElem?_getD, hl _ h]
    · rw [ite_eq_right h, ite_eq_right h, ← List.getD_eq_getElem?_getD, hl _ (by omega_using [hi, h])]
  have hm (f : Nat → BitVec 128) : ((List.range 8).map f).getD e 0 = f e := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]; rfl
  cases op <;> dsimp only
  case zip1 => rw [VG.Proof.Blowfish.AArch64.getD_pairs _ _ _ 4 e (by omega_using [he])]; split <;> rw [hl _ (by omega_using [he])]
  case zip2 => rw [VG.Proof.Blowfish.AArch64.getD_pairs _ _ _ 4 e (by omega_using [he])]; split <;> rw [hl _ (by omega_using [he])]
  case trn1 =>
    rw [VG.Proof.Blowfish.AArch64.getD_pairs _ _ _ 4 e (by omega_using [he])]
    split <;> rename_i h <;> rw [hl _ (by omega_using [he])] <;> exact congrArg _ (by omega_using [h])
  case trn2 =>
    rw [VG.Proof.Blowfish.AArch64.getD_pairs _ _ _ 4 e (by omega_using [he])]
    split <;> rename_i h <;> rw [hl _ (by omega_using [he])] <;> exact congrArg _ (by omega_using [h])
  case uzp1 =>
    rw [hm, hu (by omega_using [he])]
    by_cases h : e < 4
    · rw [ite_eq_left h, ite_eq_left (by omega_using [h])]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h])]
  case uzp2 =>
    rw [hm, hu (by omega_using [he])]
    by_cases h : e < 4
    · rw [ite_eq_left h, ite_eq_left (by omega_using [h])]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h])]; exact congrArg _ (by omega_using [h])

theorem vword_zip_zero {x z : BitVec 128} (hz : ∀ e < 8, vhalf z e = 0) {k : Nat} (hk : k < 4) :
    (vword (VPermOp.zip1.eval VArr.h8 x z) k).toNat = (vhalf x k).toNat ∧
      (vword (VPermOp.zip2.eval VArr.h8 x z) k).toNat = (vhalf x (4 + k)).toNat := by
  have h0 (v : BitVec 16) : ((0#16 : BitVec 16) ++ v : BitVec 32).toNat = v.toNat := by
    rw [BitVec.toNat_append]; simp
  constructor
  · rw [vword_halves, vhalf_perm_h8 _ _ _ (by omega_using [hk]), vhalf_perm_h8 _ _ _ (by omega_using [hk])]
    simp only [show ¬ (2 * k + 1) % 2 = 0 by omega_using [], show 2 * k % 2 = 0 by omega_using [], ↓reduceIte,
      hz _ (show (2 * k + 1) / 2 < 8 by omega_using [hk]), show 2 * k / 2 = k by omega_using []]
    exact h0 _
  · rw [vword_halves, vhalf_perm_h8 _ _ _ (by omega_using [hk]), vhalf_perm_h8 _ _ _ (by omega_using [hk])]
    simp only [show ¬ (2 * k + 1) % 2 = 0 by omega_using [], show 2 * k % 2 = 0 by omega_using [], ↓reduceIte,
      hz _ (show 4 + (2 * k + 1) / 2 < 8 by omega_using [hk]), show 2 * k / 2 = k by omega_using []]
    exact h0 _

/-- A vector read from memory, as its two doublewords. -/
theorem read16_dw (m : Mem) (a : Addr) : m.read a 16 = ofVDwords (m.readW a 64) (m.readW (a + 8#64) 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_read m 16 a j hj]
  simp only [ofVDwords, BitVec.getLsbD_append, Mem.readW, BitVec.getLsbD_setWidth]
  by_cases h : j < 64
  · simp only [h, ↓reduceIte, decide_true, Bool.true_and]
    rw [getLsbD_read m 8 a j h]
  · have h' : j - 64 < 64 := by omega_using [hj]
    simp only [h, h', ↓reduceIte, decide_true, Bool.true_and]
    rw [getLsbD_read m 8 _ _ h', BitVec.add_assoc, show 8#64 = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      show 8 + (j - 64) / 8 = j / 8 by omega_using [h], show (j - 64) % 8 = j % 8 by omega_using [h]]

end VG.Proof.MlKem.AArch64.Ntt16
