import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

/-!
# Byte and word lanes of AdvSIMD permutations

The bytes of `uzp1`/`uzp2`/`zip1`/`zip2` of `.16b` vectors, and the words of
those of `.4s` vectors, in terms of their operands' lanes; the bytes of
`rev32 .16b` and of a 16-byte load; and a word's bytes.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

theorem vbyte_read16 (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  rw [getLsbD_read m 16 a (8 * e + r) (by omega_arith), show (8 * e + r) / 8 = e by omega_arith,
    show (8 * e + r) % 8 = r by omega_arith]

theorem setWidth_setWidth8 (x : BitVec 8) : (x.setWidth 128).setWidth 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem setWidth_setWidth32 (x : BitVec 32) : (x.setWidth 128).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem b16_lanes_getD (x : BitVec 128) {i : Nat} (hi : i < 16) :
    (VArr.b16.lanes x).getD i 0 = (vbyte x i).setWidth 128 := by
  simp [VArr.lanes, List.getD_eq_getElem?_getD, hi]

theorem b16_lanes_length (x : BitVec 128) : (VArr.b16.lanes x).length = 16 := by
  simp [VArr.lanes]

theorem b16_append_getD (x y : BitVec 128) {i : Nat} (hi : i < 32) :
    (VArr.b16.lanes x ++ VArr.b16.lanes y).getD i 0 =
      if i < 16 then (vbyte x i).setWidth 128 else (vbyte y (i - 16)).setWidth 128 := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    rw [List.getElem?_append_left (by rw [b16_lanes_length]; exact h), ← List.getD_eq_getElem?_getD,
      b16_lanes_getD _ h]
  · rename_i h
    rw [List.getElem?_append_right (by rw [b16_lanes_length]; omega_arith), b16_lanes_length,
      ← List.getD_eq_getElem?_getD, b16_lanes_getD _ (by omega_arith)]

theorem vbyte_uzp1 (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval .uzp1 .b16 x y) e = if e < 8 then vbyte x (2 * e) else vbyte y (2 * e - 16) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vbyte_ofVBytes _ he]
  simp only [b16_lanes_length, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    he, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, b16_append_getD _ _ (by omega_arith)]
  by_cases h : e < 8
  · simp [h, show 2 * e < 16 by omega_arith]
  · simp [h, show ¬ 2 * e < 16 by omega_arith]

theorem vbyte_uzp2 (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval .uzp2 .b16 x y) e =
      if e < 8 then vbyte x (2 * e + 1) else vbyte y (2 * e + 1 - 16) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vbyte_ofVBytes _ he]
  simp only [b16_lanes_length, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    he, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, b16_append_getD _ _ (by omega_arith)]
  by_cases h : e < 8
  · simp [h, show 2 * e + 1 < 16 by omega_arith]
  · simp [h, show ¬ 2 * e + 1 < 16 by omega_arith]

theorem pairs_length {α : Type} (f g : Nat → α) :
    ∀ k, ((List.range k).flatMap fun p => [f p, g p]).length = 2 * k
  | 0 => rfl
  | k + 1 => by rw [List.range_succ, List.flatMap_append, List.length_append, pairs_length f g k]; simp; omega_arith

theorem getD_pairs {α : Type} (f g : Nat → α) (d : α) :
    ∀ (k e : Nat), e < 2 * k →
      ((List.range k).flatMap fun p => [f p, g p]).getD e d = if e % 2 = 0 then f (e / 2) else g (e / 2)
  | 0, _, h => absurd h (by omega_arith)
  | k + 1, e, h => by
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    have hl := pairs_length f g k
    by_cases he : e < 2 * k
    · rw [List.getElem?_append_left (by rw [hl]; exact he), ← List.getD_eq_getElem?_getD,
        getD_pairs f g d k e he]
    · rw [List.getElem?_append_right (by rw [hl]; omega_arith), hl]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rcases (by omega_arith : e = 2 * k ∨ e = 2 * k + 1) with rfl | rfl
      · simp
      · simp [show (2 * k + 1) % 2 = 1 by omega_arith, show (2 * k + 1) / 2 = k by omega_arith]

theorem vbyte_zip1 (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval .zip1 .b16 x y) e = if e % 2 = 0 then vbyte x (e / 2) else vbyte y (e / 2) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vbyte_ofVBytes _ he, b16_lanes_length, show 16 / 2 = 8 from rfl,
    getD_pairs _ _ _ 8 e (by omega_arith)]
  split <;> rw [b16_lanes_getD _ (by omega_arith), setWidth_setWidth8]

theorem vbyte_zip2 (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval .zip2 .b16 x y) e =
      if e % 2 = 0 then vbyte x (8 + e / 2) else vbyte y (8 + e / 2) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vbyte_ofVBytes _ he, b16_lanes_length, show 16 / 2 = 8 from rfl,
    getD_pairs _ _ _ 8 e (by omega_arith)]
  split <;> rw [b16_lanes_getD _ (by omega_arith), setWidth_setWidth8]

theorem s4_lanes_getD (x : BitVec 128) {i : Nat} (hi : i < 4) :
    (VArr.s4.lanes x).getD i 0 = (vword x i).setWidth 128 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem s4_ofLanes (ls : List (BitVec 128)) {e : Nat} (he : e < 4) :
    vword (VArr.s4.ofLanes ls) e = (ls.getD e 0).setWidth 32 := by
  simp only [VArr.ofLanes]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (by omega_arith : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_uzp1 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .uzp1 .s4 x y) e = if e < 2 then vword x (2 * e) else vword y (2 * e - 4) := by
  simp only [VPermOp.eval]
  rw [s4_ofLanes _ he]
  rcases (by omega_arith : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
    simp [VArr.lanes]

theorem vword_uzp2 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .uzp2 .s4 x y) e =
      if e < 2 then vword x (2 * e + 1) else vword y (2 * e + 1 - 4) := by
  simp only [VPermOp.eval]
  rw [s4_ofLanes _ he]
  rcases (by omega_arith : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
    simp [VArr.lanes]

theorem vword_zip1 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x y) e =
      if e % 2 = 0 then vword x (e / 2) else vword y (e / 2) := by
  simp only [VPermOp.eval]
  rw [s4_ofLanes _ he, show (VArr.s4.lanes x).length / 2 = 2 by simp [VArr.lanes], getD_pairs _ _ _ 2 e (by omega_arith)]
  split <;> rw [s4_lanes_getD _ (by omega_arith), setWidth_setWidth32]

theorem vword_zip2 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip2 .s4 x y) e =
      if e % 2 = 0 then vword x (2 + e / 2) else vword y (2 + e / 2) := by
  simp only [VPermOp.eval]
  rw [s4_ofLanes _ he, show (VArr.s4.lanes x).length / 2 = 2 by simp [VArr.lanes], getD_pairs _ _ _ 2 e (by omega_arith)]
  split <;> rw [s4_lanes_getD _ (by omega_arith), setWidth_setWidth32]

theorem vbyte_rev32b (x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VRevOp.eval .rev32b x) e = vbyte x (4 * (e / 4) + (3 - e % 4)) := by
  simp only [VRevOp.eval]
  rw [vbyte_ofVBytes _ he]

/-- Byte `b` of word `l` is byte `4 l + b` of the vector. -/
theorem vbyte_word (x : BitVec 128) {l b : Nat} (hb : b < 4) :
    vbyte x (4 * l + b) = (vword x l).extractLsb' (8 * b) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 8 * b + i < 32 by omega_arith]
  congr 1; omega_arith

/-- Two words with the same bytes are the same. -/
theorem word_ext {x y : BitVec 32} (h : ∀ b < 4, x.extractLsb' (8 * b) 8 = y.extractLsb' (8 * b) 8) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun z : BitVec 8 => z.getLsbD (i % 8)) (h (i / 8) (by omega_arith))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega_arith, decide_true, Bool.true_and,
    show 8 * (i / 8) + i % 8 = i by omega_arith] at this
  exact this

theorem vbyte_xor (x y : BitVec 128) (e : Nat) : vbyte (x ^^^ y) e = vbyte x e ^^^ vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vword_xor (x y : BitVec 128) (e : Nat) : vword (x ^^^ y) e = vword x e ^^^ vword y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi]

end VG.Proof.Blowfish.AArch64
