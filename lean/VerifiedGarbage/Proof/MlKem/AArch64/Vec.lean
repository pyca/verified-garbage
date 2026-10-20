module

public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint

/-!
# ML-KEM on AArch64: vectors

What the vector code needs (`Impl/MlKem/AArch64/Ntt.lean`, "Vectors"): a
16-byte load or store is four 32-bit words (`read16`, `write16`), the lanes of
the results of the vector instructions (`vword_*`), weakest-precondition rules
for them (`wp_vop`, `wp_ldrq`, `wp_strq`), and that code without them keeps
the vector registers (`WP.keepV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-! ## Memory -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by bdd_omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by bdd_omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by bdd_omega
      have e2 : (i - 8) % 8 = i % 8 := by bdd_omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem getLsbD_readW32 (m : Mem) (a : Addr) (k : Nat) {j : Nat} (hj : j < 32) :
    (m.readW (a + BitVec.ofNat 64 (4 * k)) 32).getLsbD j =
      (m (a + BitVec.ofNat 64 ((32 * k + j) / 8))).getLsbD ((32 * k + j) % 8) := by
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  rw [show 32 / 8 = 4 from rfl, getLsbD_read m 4 _ j (by bdd_omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * k + j / 8 = (32 * k + j) / 8 by bdd_omega, show j % 8 = (32 * k + j) % 8 by bdd_omega]

theorem read16 (m : Mem) (a : Addr) :
    m.read a 16 = ofVWords (m.readW (a + BitVec.ofNat 64 (4 * 0)) 32) (m.readW (a + BitVec.ofNat 64 (4 * 1)) 32)
      (m.readW (a + BitVec.ofNat 64 (4 * 2)) 32) (m.readW (a + BitVec.ofNat 64 (4 * 3)) 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read m 16 a i (by bdd_omega)]
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp only [h0]; rw [getLsbD_readW32 m a 0 h0]; simp
  by_cases h1 : i - 32 < 32
  · simp only [h0, h1]
    rw [getLsbD_readW32 m a 1 h1, show 32 * 1 + (i - 32) = i by bdd_omega]; simp
  by_cases h2 : i - 32 - 32 < 32
  · simp only [h0, h1, h2]
    rw [getLsbD_readW32 m a 2 h2, show 32 * 2 + (i - 32 - 32) = i by bdd_omega]; simp
  · simp only [h0, h1, h2]
    rw [getLsbD_readW32 m a 3 (by bdd_omega), show 32 * 3 + (i - 32 - 32 - 32) = i by bdd_omega]; simp

theorem toNat_sub_c (d : BitVec 64) (c : Nat) (hc : c < 16) :
    (d - BitVec.ofNat 64 c).toNat = if c ≤ d.toNat then d.toNat - c else 2 ^ 64 + d.toNat - c := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := d.isLt
  split <;> omega

/-- The low word of a 64-bit load. -/
theorem readW64_lo (m : Mem) (a : Addr) : (m.readW a 64).extractLsb' 0 32 = m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add, Mem.readW,
    BitVec.getLsbD_setWidth, show i < 64 by bdd_omega]
  rw [getLsbD_read m _ a i (by bdd_omega), getLsbD_read m _ a i (by bdd_omega)]

/-- The high word of a 64-bit load. -/
theorem readW64_hi (m : Mem) (a : Addr) :
    (m.readW a 64).extractLsb' 32 32 = m.readW (a + BitVec.ofNat 64 4) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Mem.readW,
    BitVec.getLsbD_setWidth, show 32 + i < 64 by bdd_omega]
  rw [getLsbD_read m _ a (32 + i) (by bdd_omega), getLsbD_read m _ _ i (by bdd_omega), BitVec.add_assoc,
    ← BitVec.ofNat_add, show 4 + i / 8 = (32 + i) / 8 by bdd_omega, show i % 8 = (32 + i) % 8 by bdd_omega]

theorem write16 (m : Mem) (a : Addr) (w0 w1 w2 w3 : BitVec 32) :
    m.write a 16 (ofVWords w0 w1 w2 w3) =
      (((m.writeW a w0).writeW (a + BitVec.ofNat 64 4) w1).writeW (a + BitVec.ofNat 64 8) w2).writeW
        (a + BitVec.ofNat 64 12) w3 :=
  VG.AArch64.write16 m a w0 w1 w2 w3

/-! ## Lanes -/

theorem vword_ofVWords (w0 w1 w2 w3 : BitVec 32) {e : Nat} (he : e < 4) :
    vword (ofVWords w0 w1 w2 w3) e = [w0, w1, w2, w3][e] := by
  ext i hi
  simp only [vword, ofVWords, BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;>
    simp +arith [hi]

/-- Two vectors with the same lanes are the same. -/
theorem vec_ext {x y : BitVec 128} (h : ∀ e < 4, vword x e = vword y e) : x = y := by
  ext i hi
  have := congrArg (fun w : BitVec 32 => w.getLsbD (i % 32)) (h (i / 32) (by bdd_omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show i % 32 < 32 by bdd_omega, decide_true,
    Bool.true_and, show 32 * (i / 32) + i % 32 = i by bdd_omega] at this
  simpa [BitVec.getElem_eq_testBit_toNat, BitVec.getLsbD] using this

theorem ofVWords_vword (x : BitVec 128) : ofVWords (vword x 0) (vword x 1) (vword x 2) (vword x 3) = x :=
  vec_ext fun e he => by
    rw [vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The lanes of the result of an operation on the lanes of two vectors. -/
theorem vword_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 4) : vword (VArr.s4.map2 f x y) e = f 32 (vword x e) (vword y e) := by
  simp only [VArr.map2]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_mapWords3 (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x y z : BitVec 128)
    {e : Nat} (he : e < 4) : vword (mapWords3 f x y z) e = f (vword x e) (vword y e) (vword z e) := by
  simp only [mapWords3]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

private theorem sw32 (w : BitVec 32) : (w.setWidth 128).setWidth 32 = w := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

private theorem sw64 (w : BitVec 64) : (w.setWidth 128).setWidth 64 = w := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

private theorem itT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

private theorem itF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

private theorem ofVWords_congr {a b c d a' b' c' d' : BitVec 32} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : ofVWords a b c d = ofVWords a' b' c' d' := by subst ha hb hc hd; rfl

private theorem ofVDwords_congr {a b a' b' : BitVec 64} (ha : a = a') (hb : b = b') :
    ofVDwords a b = ofVDwords a' b' := by subst ha hb; rfl

/-- Word `e` of two doublewords: word `e % 2` of doubleword `e / 2`. -/
private theorem vword_ofVDwords (a b : BitVec 64) {e : Nat} (he : e < 4) :
    vword (ofVDwords a b) e = (if e < 2 then a else b).extractLsb' (32 * (e % 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vword, ofVDwords, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : e < 2
  · rw [itT h, itT (show 32 * e + i < 64 by bdd_omega)]; exact congrArg _ (by bdd_omega)
  · rw [itF h, itF (show ¬ 32 * e + i < 64 by bdd_omega)]; exact congrArg _ (by bdd_omega)

/-- Word `j` of doubleword `k`: word `2k + j`. -/
private theorem vdword_word (x : BitVec 128) (k : Nat) {j : Nat} (hj : j < 2) :
    (vdword x k).extractLsb' (32 * j) 32 = vword x (2 * k + j) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vword, vdword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 32 * j + i < 64 by bdd_omega]
  exact congrArg _ (by bdd_omega)

private theorem eval_trn1_d2 (x y : BitVec 128) :
    VPermOp.eval .trn1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv]
  exact ofVDwords_congr (sw64 (vdword x 0)) (sw64 (vdword y 0))

private theorem eval_trn2_d2 (x y : BitVec 128) :
    VPermOp.eval .trn2 .d2 x y = ofVDwords (vdword x 1) (vdword y 1) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv]
  exact ofVDwords_congr (sw64 (vdword x 1)) (sw64 (vdword y 1))

theorem vword_trn1_d2 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .trn1 .d2 x y) e = if e < 2 then vword x e else vword y (e - 2) := by
  rw [eval_trn1_d2, vword_ofVDwords _ _ he]
  by_cases h : e < 2
  · rw [itT h, itT h, vdword_word _ _ (Nat.mod_lt _ (by decide))]; exact congrArg _ (by bdd_omega)
  · rw [itF h, itF h, vdword_word _ _ (Nat.mod_lt _ (by decide))]; exact congrArg _ (by bdd_omega)

theorem vword_trn2_d2 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .trn2 .d2 x y) e = if e < 2 then vword x (e + 2) else vword y e := by
  rw [eval_trn2_d2, vword_ofVDwords _ _ he]
  by_cases h : e < 2
  · rw [itT h, itT h, vdword_word _ _ (Nat.mod_lt _ (by decide))]; exact congrArg _ (by bdd_omega)
  · rw [itF h, itF h, vdword_word _ _ (Nat.mod_lt _ (by decide))]; exact congrArg _ (by bdd_omega)

theorem vword_dup_d2 (g : BitVec 64) {e : Nat} (he : e < 4) :
    vword (ofVDwords g g) e = g.extractLsb' (32 * (e % 2)) 32 := by
  rw [vword_ofVDwords _ _ he]
  by_cases h : e < 2
  · rw [itT h]
  · rw [itF h]

private theorem eval_zip1_s4 (x y : BitVec 128) :
    VPermOp.eval .zip1 .s4 x y = ofVWords (vword x 0) (vword y 0) (vword x 1) (vword y 1) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv]
  exact ofVWords_congr (sw32 (vword x 0)) (sw32 (vword y 0)) (sw32 (vword x 1)) (sw32 (vword y 1))

private theorem eval_zip2_s4 (x y : BitVec 128) :
    VPermOp.eval .zip2 .s4 x y = ofVWords (vword x 2) (vword y 2) (vword x 3) (vword y 3) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv]
  exact ofVWords_congr (sw32 (vword x 2)) (sw32 (vword y 2)) (sw32 (vword x 3)) (sw32 (vword y 3))

private theorem eval_uzp1_s4 (x y : BitVec 128) :
    VPermOp.eval .uzp1 .s4 x y = ofVWords (vword x 0) (vword x 2) (vword y 0) (vword y 2) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd]
  exact ofVWords_congr (sw32 (vword x 0)) (sw32 (vword x 2)) (sw32 (vword y 0)) (sw32 (vword y 2))

private theorem eval_uzp2_s4 (x y : BitVec 128) :
    VPermOp.eval .uzp2 .s4 x y = ofVWords (vword x 1) (vword x 3) (vword y 1) (vword y 3) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd]
  exact ofVWords_congr (sw32 (vword x 1)) (sw32 (vword x 3)) (sw32 (vword y 1)) (sw32 (vword y 3))

theorem vword_zip1_s4 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x x) e = vword x (e / 2) := by
  rw [eval_zip1_s4, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_uzp1_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .uzp1 .s4 x y) e = if e < 2 then vword x (2 * e) else vword y (2 * (e - 2)) := by
  rw [eval_uzp1_s4, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_uzp2_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .uzp2 .s4 x y) e =
      if e < 2 then vword x (2 * e + 1) else vword y (2 * (e - 2) + 1) := by
  rw [eval_uzp2_s4, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_zip1_s4' (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x y) e = if e % 2 = 0 then vword x (e / 2) else vword y (e / 2) := by
  rw [eval_zip1_s4, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_zip2_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip2 .s4 x y) e =
      if e % 2 = 0 then vword x (2 + e / 2) else vword y (2 + e / 2) := by
  rw [eval_zip2_s4, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
private theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat}
    (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by bdd_omega)
    simp only [hk, show ¬ n * k + r < n by bdd_omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

private theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by bdd_omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem vword_rev64s (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VRevOp.eval .rev64s x) e = vword x (if e % 2 = 0 then e + 1 else e - 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vword, VRevOp.eval, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [show 32 * e + i = 8 * (4 * e + i / 8) + i % 8 by bdd_omega,
    getLsbD_ofVBytes _ (by bdd_omega) (Nat.mod_lt _ (by decide)), vbyte, BitVec.getLsbD_extractLsb',
    decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and]
  exact congrArg _ (by split <;> omega)

theorem vword_dup_s4 (w : BitVec 32) {e : Nat} (he : e < 4) : vword (ofVWords w w w w) e = w := by
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;> rfl

/-- SQDMULH on lanes less than `2³¹`: `⌊a · b / 2³¹⌋`, without saturating. -/
theorem sqdmulhLane_lt {a b : BitVec 32} (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) :
    sqdmulhLane a b = some (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 31)) := by
  have hne : ¬ (a = 0x80000000#32 ∧ b = 0x80000000#32) := fun h => by
    rw [h.1] at ha; exact absurd ha (by decide)
  simp only [sqdmulhLane, hne, ite_false, Option.some.injEq]
  rw [BitVec.toInt_eq_toNat_of_lt (by bdd_omega), BitVec.toInt_eq_toNat_of_lt (by bdd_omega),
    show (2 : Int) * a.toNat * b.toNat = ((2 * a.toNat * b.toNat : Nat) : Int) by push_cast; rfl,
    ← Int.natCast_shiftRight, BitVec.ofInt_natCast, Nat.shiftRight_eq_div_pow,
    show 2 * a.toNat * b.toNat / 2 ^ 32 = a.toNat * b.toNat / 2 ^ 31 by rw [Nat.mul_assoc]; omega]

/-! ## Instructions -/

/-- `s'` is `s` with the vector register `d` set to `x`. -/
structure VUpd (s s' : State) (d : VReg) (x : BitVec 128) : Prop where
  v : s'.v d = x
  other : ∀ r, r ≠ d → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- A vector register other than `d` is kept. -/
theorem VUpd.get {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) (r : VReg)
    (hr : r ≠ d := by decide) : s'.v r = s.v r := h.other r hr

theorem VUpd.keep {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) (hd : d ∉ preservedV := by decide +kernel) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r hr => by rw [h.other r (fun e => hd (e ▸ hr))]⟩

theorem vupd_setV (s : State) (d : VReg) (x : BitVec 128) : VUpd s (s.setV d x) d x :=
  ⟨by simp [State.setV], fun r h => by simp [State.setV, h], rfl, rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure VMem (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  v : s'.v = s.v
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vop {op : VOp} {d : VReg} {x : BitVec 128} (he : op.eval s = some (d, x))
    (k : ∀ s', VUpd s s' d x → WP isa (.block is) s' Q) : WP isa (.block (.vop op :: is)) s Q :=
  WP.cons (s' := s.setV d x) (by simp only [exec, he, Option.map_some]) (k _ (vupd_setV s d x))

theorem wp_ldrq {t : VReg} {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', VUpd s s' t (s.mem.read a 16) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrq t n off :: is)) s Q :=
  WP.cons (s' := s.setV t (s.mem.read a 16))
    (by simp only [exec, addr, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
      Option.map_some]) (k _ (vupd_setV _ _ _))

theorem wp_strq {t : VReg} {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', VMem s s' (s.mem.write a 16 (s.v t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strq t n off :: is)) s Q :=
  WP.cons (s' := { s with mem := s.mem.write a 16 (s.v t) })
    (by simp only [exec, addr, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Whether an instruction writes a vector register. -/
def writesV : Instr → Bool
  | .vop _ | .ldrq .. | .ldrqTbl .. => true
  | _ => false

theorem exec_v {i : Instr} (hi : writesV i = false) {s s' : State} (h : exec i s = some s') :
    s'.v = s.v :=
  have hd : vdstOf i = none := by cases i <;> first | rfl | cases hi
  funext fun _ => exec_vec (by rw [hd]; exact nofun) h

/-- Code that writes no vector register keeps them. -/
theorem WP.keepV : ∀ {is : List Instr} {s : State} {Q : State → Prop},
    (is.all fun i => !writesV i) = true → WP isa (.block is) s Q →
      WP isa (.block is) s fun s' => Q s' ∧ s'.v = s.v
  | [], _, _, _, h => WP.block_nil_iff.mpr ⟨WP.block_nil_iff.mp h, rfl⟩
  | _ :: _, _, _, hno, h => by
    obtain ⟨s₁, he, h₁⟩ := WP.block_cons_iff.mp h
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hno
    exact WP.block_cons_iff.mpr ⟨s₁, he, WP.mono (WP.keepV hno.2 h₁) fun _ ⟨hq, hv⟩ =>
      ⟨hq, hv.trans (exec_v hno.1 he)⟩⟩

/-- Scalar code `is`, proved with the scalar rules, keeps the vector
registers for the code after it. -/
theorem wp_scalar {is rest : List Instr} {s : State} {P Q : State → Prop}
    (hno : (is.all fun i => !writesV i) = true) (h : WP isa (.block is) s P)
    (hq : ∀ s', P s' → s'.v = s.v → WP isa (.block rest) s' Q) : WP isa (.block (is ++ rest)) s Q := by
  rw [WP.block_append_iff]
  exact WP.mono (WP.keepV hno h) fun s' ⟨p, v⟩ => hq s' p v

/-! ## Arithmetic modulo `q` -/

/-- `min(d, d - q)` in 32 bits is `d mod q`, for `d < 2q`. -/
theorem csub_nat {d : Nat} (h : d < 2 * 3329) : min d ((d + (2 ^ 32 - 3329)) % 2 ^ 32) = d % 3329 := by
  omega

private theorem barrett_sum (t : Nat) :
    (t * 2147483648 + 2147483648) * 3329 + 3329 * 2147483648 = (t * 3329 + 2 * 3329) * 2147483648 := by
  omega

/-- Barrett reduction with `M = ⌊2³¹ / q⌋ = 645083`: `t = ⌊x · M / 2³¹⌋` is at
most `x / q`, and more than `x / q - 2`. -/
theorem barrett_nat {x : Nat} (hx : x < 2147483648) :
    x * 645083 / 2147483648 * 3329 ≤ x ∧ x < x * 645083 / 2147483648 * 3329 + 2 * 3329 := by
  have h1 := Nat.div_mul_le_self (x * 645083) 2147483648
  have h2 := Nat.lt_div_mul_add (a := x * 645083) (b := 2147483648) (by decide)
  generalize x * 645083 / 2147483648 = t at h1 h2 ⊢
  constructor
  · have : t * 3329 * 2147483648 ≤ x * 2147483648 := by
      calc t * 3329 * 2147483648 = t * 2147483648 * 3329 := by rw [Nat.mul_right_comm]
        _ ≤ x * 645083 * 3329 := Nat.mul_le_mul_right _ h1
        _ ≤ x * 2147483648 := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by decide)
    exact Nat.le_of_mul_le_mul_right this (by decide)
  · have : x * 2147483648 < (t * 3329 + 2 * 3329) * 2147483648 := by
      have e : x * 645083 * 3329 + x * 2341 = x * 2147483648 := by
        rw [Nat.mul_assoc, ← Nat.mul_add]
      have h3 : x * 645083 * 3329 < (t * 2147483648 + 2147483648) * 3329 :=
        Nat.mul_lt_mul_of_pos_right h2 (by decide)
      have h4 : x * 2341 < 3329 * 2147483648 :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx (by decide)) (by decide)
      calc x * 2147483648 = x * 645083 * 3329 + x * 2341 := e.symm
        _ < (t * 2147483648 + 2147483648) * 3329 + 3329 * 2147483648 := Nat.add_lt_add h3 h4
        _ = (t * 3329 + 2 * 3329) * 2147483648 := barrett_sum t
    exact Nat.lt_of_mul_lt_mul_right this

/-! ## Lanes as numbers -/

/-- The lanes of `x` are `f 0`, …, `f 3`. -/
def Lanes (x : BitVec 128) (f : Nat → Nat) : Prop := ∀ e < 4, (vword x e).toNat = f e

theorem Lanes.lt {x : BitVec 128} {f : Nat → Nat} (h : Lanes x f) {e : Nat} (he : e < 4) :
    f e < 2 ^ 32 := by rw [← h e he]; exact (vword x e).isLt

theorem Lanes.congr {x : BitVec 128} {f g : Nat → Nat} (h : Lanes x f) (hfg : ∀ e < 4, f e = g e) :
    Lanes x g := fun e he => (h e he).trans (hfg e he)

theorem lanes_add {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => a + b) x y) fun e => (f e + g e) % 2 ^ 32 := fun e he => by
  rw [vword_map2 _ _ _ he, BitVec.toNat_add, hx e he, hy e he]

theorem lanes_sub {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => a - b) x y) fun e => (2 ^ 32 - g e + f e) % 2 ^ 32 := fun e he => by
  rw [vword_map2 _ _ _ he, BitVec.toNat_sub, hx e he, hy e he]

theorem lanes_mul {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => a * b) x y) fun e => f e * g e % 2 ^ 32 := fun e he => by
  rw [vword_map2 _ _ _ he, BitVec.toNat_mul, hx e he, hy e he]

theorem lanes_umin {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => if a.toNat ≤ b.toNat then a else b) x y) fun e => min (f e) (g e) :=
  fun e he => by
    show _ = min (f e) (g e)
    rw [vword_map2 _ _ _ he]
    split <;> rename_i h <;> rw [hx e he, hy e he] at * <;> omega

theorem lanes_mls {a x y : BitVec 128} {h f g : Nat → Nat} (ha : Lanes a h) (hx : Lanes x f)
    (hy : Lanes y g) :
    Lanes (mapWords3 (fun a x y => a - x * y) a x y) fun e => (2 ^ 32 - f e * g e % 2 ^ 32 + h e) % 2 ^ 32 :=
  fun e he => by
    rw [vword_mapWords3 _ _ _ _ he, BitVec.toNat_sub, BitVec.toNat_mul, ha e he, hx e he, hy e he]

theorem lanes_mla {a x y : BitVec 128} {h f g : Nat → Nat} (ha : Lanes a h) (hx : Lanes x f)
    (hy : Lanes y g) :
    Lanes (mapWords3 (fun a x y => a + x * y) a x y) fun e => (h e + f e * g e % 2 ^ 32) % 2 ^ 32 :=
  fun e he => by
    rw [vword_mapWords3 _ _ _ _ he, BitVec.toNat_add, BitVec.toNat_mul, ha e he, hx e he, hy e he]

theorem lanes_dup {w : BitVec 32} : Lanes (ofVWords w w w w) fun _ => w.toNat := fun e he => by
  rw [vword_dup_s4 w he]

theorem eval_sqdmulh {s : State} {d n m : VReg} {f g : Nat → Nat} (hn : Lanes (s.v n) f)
    (hm : Lanes (s.v m) g) (hf : ∀ e < 4, f e < 2 ^ 31) (hg : ∀ e < 4, g e < 2 ^ 31) :
    ∃ x, VOp.eval s (.sqdmulh d n m) = some (d, x) ∧ Lanes x fun e => f e * g e / 2 ^ 31 := by
  have l : ∀ e < 4, sqdmulhLane (vword (s.v n) e) (vword (s.v m) e) =
      some (BitVec.ofNat 32 (f e * g e / 2 ^ 31)) := fun e he => by
    rw [sqdmulhLane_lt (by rw [hn e he]; exact hf e he) (by rw [hm e he]; exact hg e he), hn e he, hm e he]
  refine ⟨ofVWords (BitVec.ofNat 32 (f 0 * g 0 / 2 ^ 31)) (BitVec.ofNat 32 (f 1 * g 1 / 2 ^ 31))
      (BitVec.ofNat 32 (f 2 * g 2 / 2 ^ 31)) (BitVec.ofNat 32 (f 3 * g 3 / 2 ^ 31)),
    by simp only [VOp.eval, l 0 (by decide), l 1 (by decide), l 2 (by decide), l 3 (by decide)],
    fun e he => ?_⟩
  have hl : f e * g e / 2 ^ 31 < 2 ^ 32 := by
    have h1 := hf e he
    have h2 := hg e he
    exact Nat.lt_of_le_of_lt (Nat.div_le_div_right (c := 2 ^ 31)
      (Nat.mul_le_mul (Nat.le_of_lt h1) (Nat.le_of_lt h2))) (by decide)
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by bdd_omega) with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]

/-! ## The arithmetic of the vector code -/

/-- `s'` is `s` but for the vector registers `rs`. -/
structure VChg (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace VChg

theorem refl (rs : List VReg) (s : State) : VChg rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List VReg} {s₁ s₂ s₃ : State} (h₁ : VChg rs s₁ s₂) (h₂ : VChg rs' s₂ s₃) :
    VChg (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.v r hr.2, h₁.v r hr.1],
   h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List VReg} {s s' : State} (h : VChg rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VChg rs' s s' :=
  ⟨fun r hr => h.v r fun h' => hr (hs r h'), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem get {rs : List VReg} {s s' : State} (h : VChg rs s s') (r : VReg) (hr : r ∉ rs := by decide) :
    s'.v r = s.v r := h.v r hr

end VChg

theorem VChg.keep {rs : List VReg} {s s' : State} (h : VChg rs s s') (hv : ∀ r ∈ preservedV, r ∉ rs := by decide +kernel) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r hr => by rw [h.v r (hv r hr)]⟩

theorem VMem.keep {s s' : State} {m : Mem} (h : VMem s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r _ => by rw [h.v]⟩

theorem VUpd.chg {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) : VChg [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

/-- `q` and `M` in the lanes of `v16` and `v17`. -/
structure VConsts (s : State) : Prop where
  q : Lanes (s.v .v16) fun _ => 3329
  m : Lanes (s.v .v17) fun _ => 645083

theorem VConsts.chg {s s' : State} (h : VConsts s) {rs : List VReg} (hc : VChg rs s s')
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide) : VConsts s' :=
  ⟨by rw [hc.get _ h16]; exact h.q, by rw [hc.get _ h17]; exact h.m⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `vcsub d t`: `d mod q`, for lanes less than `2q`. -/
theorem vcsub_ok {d t : VReg} (hdt : d ≠ t := by decide) (hq : Lanes (s.v .v16) fun _ => 3329)
    {f : Nat → Nat}
    (hf : Lanes (s.v d) f) (hlt : ∀ e < 4, f e < 2 * 3329)
    (k : ∀ s', VChg [t, d] s s' → Lanes (s'.v d) (fun e => f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (vcsub d t ++ rest)) s Q := by
  refine wp_vop (d := t) rfl fun s₁ h₁ => wp_vop (d := d) rfl fun s₂ h₂ => k s₂ (h₁.chg.trans h₂.chg) ?_
  have l₁ := lanes_sub hf hq
  rw [← h₁.v] at l₁
  rw [h₂.v]
  refine (lanes_umin (by rw [h₁.get d hdt]; exact hf) l₁).congr fun e he => ?_
  have := hlt e he
  omega

/-- `sqdmulh t, d, M; mls d, t, q`: Barrett reduction of lanes `x < 2³¹`, to
`x - ⌊x · M / 2³¹⌋ · q`, which is less than `2q` and congruent to `x`. -/
theorem vbar_ok {d t : VReg} (hdt : d ≠ t := by decide) (ht16 : t ≠ .v16 := by decide)
    (ht17 : t ≠ .v17 := by decide) (hc : VConsts s) {f : Nat → Nat} (hf : Lanes (s.v d) f)
    (hlt : ∀ e < 4, f e < 2 ^ 31)
    (k : ∀ s', VChg [t, d] s s' →
      Lanes (s'.v d) (fun e => f e - f e * 645083 / 2 ^ 31 * 3329) →
      (∀ e < 4, f e - f e * 645083 / 2 ^ 31 * 3329 < 2 * 3329 ∧
        (f e - f e * 645083 / 2 ^ 31 * 3329) % 3329 = f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (.vop (.sqdmulh t d .v17) :: .vop (.mls d t .v16) :: rest)) s Q := by
  obtain ⟨x₁, e₁, l₁⟩ := eval_sqdmulh (d := t) hf hc.m hlt (fun _ _ => by decide)
  refine wp_vop e₁ fun s₁ h₁ => ?_
  have c₁ := hc.chg h₁.chg (by simpa using ht16.symm) (by simpa using ht17.symm)
  refine wp_vop (d := d) rfl fun s₂ h₂ => ?_
  have a₁ : Lanes (s₁.v d) f := by rw [h₁.get d hdt]; exact hf
  have b₁ : Lanes (s₁.v t) fun e => f e * 645083 / 2 ^ 31 := by rw [h₁.v]; exact l₁
  have l₂ := lanes_mls a₁ b₁ c₁.q
  rw [← h₂.v] at l₂
  have hb : ∀ e < 4, f e * 645083 / 2 ^ 31 * 3329 ≤ f e ∧
      f e < f e * 645083 / 2 ^ 31 * 3329 + 2 * 3329 := fun e he => barrett_nat (hlt e he)
  refine k s₂ (h₁.chg.trans h₂.chg) (l₂.congr fun e he => ?_) fun e he => ⟨?_, ?_⟩
  · show _ = f e - f e * 645083 / 2 ^ 31 * 3329
    have := hb e he
    have : f e * 645083 / 2 ^ 31 * 3329 % 2 ^ 32 = f e * 645083 / 2 ^ 31 * 3329 :=
      Nat.mod_eq_of_lt (by have := hlt e he; omega)
    have := hlt e he
    omega
  · have := hb e he; omega
  · have hb' := (hb e he).1
    rw [Nat.mul_comm] at hb'
    rw [Nat.mul_comm _ 3329, Nat.sub_mul_mod hb']

end

end VG.Proof.MlKem.AArch64
