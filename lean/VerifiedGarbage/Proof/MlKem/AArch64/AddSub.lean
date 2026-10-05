import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
import VerifiedGarbage.Proof.MlKem.KPke1024

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Vec`. -/
section

/-!
# ML-KEM on AArch64: vectors

What the vector code needs (`Impl/MlKem/AArch64/Ntt.lean`, "Vectors"): a
16-byte load or store is four 32-bit words (`read16`, `write16`), the lanes of
the results of the vector instructions (`vword_*`), weakest-precondition rules
for them (`wp_vop`, `wp_ldrq`, `wp_strq`), and that code without them keeps
the vector registers (`WP.keepV`).
-/

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

theorem getLsbD_ofVWords (w0 w1 w2 w3 : BitVec 32) {i : Nat} (hi : i < 128) :
    (ofVWords w0 w1 w2 w3).getLsbD i =
      if i < 32 then w0.getLsbD i else if i < 64 then w1.getLsbD (i - 32)
      else if i < 96 then w2.getLsbD (i - 64) else w3.getLsbD (i - 96) := by
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp [h0]
  by_cases h1 : i < 64
  · simp [h0, h1, show i - 32 < 32 by bdd_omega]
  by_cases h2 : i < 96
  · simp [h0, h1, h2, show ¬ i - 32 < 32 by bdd_omega, show i - 32 - 32 = i - 64 by bdd_omega, show i - 64 < 32 by bdd_omega]
  · simp [h0, h1, h2, show ¬ i - 32 < 32 by bdd_omega, show ¬ i - 32 - 32 < 32 by bdd_omega,
      show i - 32 - 32 - 32 = i - 96 by bdd_omega]

theorem write16 (m : Mem) (a : Addr) (w0 w1 w2 w3 : BitVec 32) :
    m.write a 16 (ofVWords w0 w1 w2 w3) =
      (((m.writeW a w0).writeW (a + BitVec.ofNat 64 4) w1).writeW (a + BitVec.ofNat 64 8) w2).writeW
        (a + BitVec.ofNat 64 12) w3 := by
  funext x
  have e : ∀ c : Nat, x - (a + BitVec.ofNat 64 c) = (x - a) - BitVec.ofNat 64 c := fun c =>
    Offset.sub_add_eq x a _
  simp only [Mem.writeW, Mem.write, e, show 32 / 8 = 4 from rfl]
  generalize x - a = d
  rw [toNat_sub_c d 4 (by bdd_omega), toNat_sub_c d 8 (by bdd_omega), toNat_sub_c d 12 (by bdd_omega)]
  have := d.isLt
  have ext : ∀ (k : Nat) (w : BitVec 32), k < 4 → 4 * k ≤ d.toNat → d.toNat < 4 * k + 4 →
      (∀ b < 8, w.getLsbD (8 * (d.toNat - 4 * k) + b) = (ofVWords w0 w1 w2 w3).getLsbD (8 * d.toNat + b)) →
      (ofVWords w0 w1 w2 w3).extractLsb' (8 * d.toNat) 8 =
        (w.setWidth (8 * 4)).extractLsb' (8 * (d.toNat - 4 * k)) 8 := by
    intro k w hk h1 h2 hw
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show 8 * (d.toNat - 4 * k) + b < 8 * 4 by bdd_omega]
    exact (hw b hb).symm
  have g := fun (b : Nat) (h : 8 * d.toNat + b < 128) => getLsbD_ofVWords w0 w1 w2 w3 h
  by_cases c3 : 12 ≤ d.toNat
  · by_cases c4 : d.toNat < 16
    · simp only [c3, c4, ite_true, show d.toNat - 12 < 4 by bdd_omega]
      refine ext 3 w3 (by bdd_omega) c3 (by bdd_omega) fun b hb => ?_
      rw [g b (by bdd_omega)]
      simp only [show ¬ 8 * d.toNat + b < 96 by bdd_omega, show ¬ 8 * d.toNat + b < 64 by bdd_omega,
        show ¬ 8 * d.toNat + b < 32 by bdd_omega, ite_false, show 8 * (d.toNat - 4 * 3) + b = 8 * d.toNat + b - 96 by bdd_omega]
    · simp only [c3, c4, ite_true, ite_false, show ¬ d.toNat - 12 < 4 by bdd_omega,
        show ¬ d.toNat - 8 < 4 by bdd_omega, show ¬ d.toNat - 4 < 4 by bdd_omega, show 8 ≤ d.toNat by bdd_omega,
        show 4 ≤ d.toNat by bdd_omega, show ¬ d.toNat < 4 by bdd_omega]
  by_cases c2 : 8 ≤ d.toNat
  · simp only [c3, c2, ite_true, ite_false, show d.toNat < 16 by bdd_omega, show d.toNat - 8 < 4 by bdd_omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by bdd_omega]
    refine ext 2 w2 (by bdd_omega) c2 (by bdd_omega) fun b hb => ?_
    rw [g b (by bdd_omega)]
    simp only [show 8 * d.toNat + b < 96 by bdd_omega, show ¬ 8 * d.toNat + b < 64 by bdd_omega,
      show ¬ 8 * d.toNat + b < 32 by bdd_omega, ite_false, ite_true,
      show 8 * (d.toNat - 4 * 2) + b = 8 * d.toNat + b - 64 by bdd_omega]
  by_cases c1 : 4 ≤ d.toNat
  · simp only [c3, c2, c1, ite_true, ite_false, show d.toNat < 16 by bdd_omega, show d.toNat - 4 < 4 by bdd_omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by bdd_omega, show ¬ 2 ^ 64 + d.toNat - 8 < 4 by bdd_omega]
    refine ext 1 w1 (by bdd_omega) c1 (by bdd_omega) fun b hb => ?_
    rw [g b (by bdd_omega)]
    simp only [show 8 * d.toNat + b < 64 by bdd_omega, show ¬ 8 * d.toNat + b < 32 by bdd_omega, ite_false,
      ite_true, show 8 * (d.toNat - 4 * 1) + b = 8 * d.toNat + b - 32 by bdd_omega]
  · simp only [c3, c2, c1, ite_true, ite_false, show d.toNat < 16 by bdd_omega, show d.toNat < 4 by bdd_omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by bdd_omega, show ¬ 2 ^ 64 + d.toNat - 8 < 4 by bdd_omega,
      show ¬ 2 ^ 64 + d.toNat - 4 < 4 by bdd_omega]
    refine ext 0 w0 (by bdd_omega) (by bdd_omega) (by bdd_omega) fun b hb => ?_
    rw [g b (by bdd_omega)]
    simp only [show 8 * d.toNat + b < 32 by bdd_omega, ite_true, show 8 * (d.toNat - 4 * 0) + b = 8 * d.toNat + b by bdd_omega]


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
structure VUpd (s s' : VG.AArch64.State) (d : VReg) (x : BitVec 128) : Prop where
  v : s'.v d = x
  other : ∀ r, r ≠ d → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- A vector register other than `d` is kept. -/
theorem VUpd.get {s s' : VG.AArch64.State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) (r : VReg)
    (hr : r ≠ d := by decide) : s'.v r = s.v r := h.other r hr

theorem VUpd.keep {s s' : VG.AArch64.State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) (hd : d ∉ VG.AArch64.preservedV := by decide +kernel) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r hr => by rw [h.other r (fun e => hd (e ▸ hr))]⟩

theorem vupd_setV (s : VG.AArch64.State) (d : VReg) (x : BitVec 128) : VUpd s (s.setV d x) d x :=
  ⟨by simp [State.setV], fun r h => by simp [State.setV, h], rfl, rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure VMem (s s' : VG.AArch64.State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  v : s'.v = s.v
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

section
variable {is : List Instr} {s : VG.AArch64.State} {Q : VG.AArch64.State → Prop}

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
  | .vop _ | .ldrq .. => true
  | _ => false

theorem exec_v {i : Instr} (hi : writesV i = false) {s s' : VG.AArch64.State} (h : exec i s = some s') :
    s'.v = s.v := by
  cases i <;> simp only [writesV, Bool.true_eq_false] at hi
  all_goals
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  all_goals
    repeat' first
      | split at h
      | simp only [Option.map_eq_some_iff] at h
      | rcases h with ⟨_, _, h⟩
  all_goals
    simp_all only [State.store]
  all_goals
    repeat' first | split at h | cases h
  all_goals rfl

/-- Code that writes no vector register keeps them. -/
theorem WP.keepV : ∀ {is : List Instr} {s : VG.AArch64.State} {Q : VG.AArch64.State → Prop},
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
theorem wp_scalar {is rest : List Instr} {s : VG.AArch64.State} {P Q : VG.AArch64.State → Prop}
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

theorem eval_sqdmulh {s : VG.AArch64.State} {d n m : VReg} {f g : Nat → Nat} (hn : Lanes (s.v n) f)
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
structure VChg (rs : List VReg) (s s' : VG.AArch64.State) : Prop where
  v : ∀ r, r ∉ rs → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace VChg

theorem refl (rs : List VReg) (s : VG.AArch64.State) : VChg rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List VReg} {s₁ s₂ s₃ : VG.AArch64.State} (h₁ : VChg rs s₁ s₂) (h₂ : VChg rs' s₂ s₃) :
    VChg (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.v r hr.2, h₁.v r hr.1],
   h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List VReg} {s s' : VG.AArch64.State} (h : VChg rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VChg rs' s s' :=
  ⟨fun r hr => h.v r fun h' => hr (hs r h'), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem get {rs : List VReg} {s s' : VG.AArch64.State} (h : VChg rs s s') (r : VReg) (hr : r ∉ rs := by decide) :
    s'.v r = s.v r := h.v r hr

end VChg

theorem VChg.keep {rs : List VReg} {s s' : VG.AArch64.State} (h : VChg rs s s') (hv : ∀ r ∈ VG.AArch64.preservedV, r ∉ rs := by decide +kernel) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r hr => by rw [h.v r (hv r hr)]⟩

theorem VMem.keep {s s' : VG.AArch64.State} {m : Mem} (h : VMem s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r _ => by rw [h.v]⟩

theorem VUpd.chg {s s' : VG.AArch64.State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) : VChg [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

/-- `q` and `M` in the lanes of `v16` and `v17`. -/
structure VConsts (s : VG.AArch64.State) : Prop where
  q : Lanes (s.v .v16) fun _ => 3329
  m : Lanes (s.v .v17) fun _ => 645083

theorem VConsts.chg {s s' : VG.AArch64.State} (h : VConsts s) {rs : List VReg} (hc : VChg rs s s')
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide) : VConsts s' :=
  ⟨by rw [hc.get _ h16]; exact h.q, by rw [hc.get _ h17]; exact h.m⟩

section
variable {rest : List Instr} {s : VG.AArch64.State} {Q : VG.AArch64.State → Prop}

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

/-- `vmulq d z t`: `d · z mod q`, for lanes less than `q`. -/
theorem vmulq_ok {d z t : VReg} (hdt : d ≠ t := by decide)
    (ht16 : t ≠ .v16 := by decide) (ht17 : t ≠ .v17 := by decide) (hd16 : d ≠ .v16 := by decide)
    (hd17 : d ≠ .v17 := by decide) (hc : VConsts s) {f g : Nat → Nat}
    (hf : Lanes (s.v d) f) (hf' : ∀ e < 4, f e < 3329) (hg : Lanes (s.v z) g) (hg' : ∀ e < 4, g e < 3329)
    (k : ∀ s', VChg [d, t, d, t, d] s s' → Lanes (s'.v d) (fun e => f e * g e % 3329) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (vmulq d z t ++ rest)) s Q := by
  have hfg : ∀ e < 4, f e * g e < 3329 * 3329 := fun e he =>
    Nat.mul_lt_mul_of_lt_of_lt (hf' e he) (hg' e he)
  refine wp_vop (d := d) rfl fun s₁ h₁ => ?_
  have l₁ : Lanes (s₁.v d) fun e => f e * g e := by
    rw [h₁.v]
    exact (lanes_mul hf hg).congr fun e he => Nat.mod_eq_of_lt (by have := hfg e he; omega)
  have c₁ := hc.chg h₁.chg (by simpa using hd16.symm) (by simpa using hd17.symm)
  obtain ⟨x₂, e₂, l₂⟩ := eval_sqdmulh (d := t) l₁ c₁.m (fun e he => by have := hfg e he; omega)
    (fun _ _ => by decide)
  refine wp_vop e₂ fun s₂ h₂ => ?_
  have c₂ := c₁.chg h₂.chg (by simpa using ht16.symm) (by simpa using ht17.symm)
  refine wp_vop (d := d) rfl fun s₃ h₃ => ?_
  have c₃ := c₂.chg h₃.chg (by simpa using hd16.symm) (by simpa using hd17.symm)
  have a₂ : Lanes (s₂.v d) fun e => f e * g e := by rw [h₂.get d hdt]; exact l₁
  have b₂ : Lanes (s₂.v t) fun e => f e * g e * 645083 / 2 ^ 31 := by rw [h₂.v]; exact l₂
  have l₃ := lanes_mls a₂ b₂ c₂.q
  rw [← h₃.v] at l₃
  have hb : ∀ e < 4, f e * g e * 645083 / 2 ^ 31 * 3329 ≤ f e * g e ∧
      f e * g e < f e * g e * 645083 / 2 ^ 31 * 3329 + 2 * 3329 := fun e he =>
    barrett_nat (by have := hfg e he; omega)
  refine vcsub_ok hdt c₃.q (f := fun e => f e * g e - f e * g e * 645083 / 2 ^ 31 * 3329)
    (l₃.congr fun e he => ?_) (fun e he => ?_) fun s₄ h₄ l₄ =>
    k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄) (l₄.congr fun e he => ?_)
  · show _ = f e * g e - f e * g e * 645083 / 2 ^ 31 * 3329
    have := hb e he
    have : f e * g e * 645083 / 2 ^ 31 * 3329 % 2 ^ 32 = f e * g e * 645083 / 2 ^ 31 * 3329 :=
      Nat.mod_eq_of_lt (by have := hfg e he; omega)
    omega
  · have := hb e he; omega
  · show (f e * g e - f e * g e * 645083 / 2 ^ 31 * 3329) % 3329 = f e * g e % 3329
    have hb' := (hb e he).1
    rw [Nat.mul_comm] at hb'
    rw [Nat.mul_comm _ 3329, Nat.sub_mul_mod hb']

/-- `vbfly z`: the butterflies of Algorithm 9 on the lanes of `v0` and `v1`. -/
theorem vbfly_ok {z : VReg} (hc : VConsts s) {A B Z : Nat → Nat} (hA : Lanes (s.v .v0) A) (hA' : ∀ e < 4, A e < 3329)
    (hB : Lanes (s.v .v1) B) (hB' : ∀ e < 4, B e < 3329) (hZ : Lanes (s.v z) Z)
    (hZ' : ∀ e < 4, Z e < 3329)
    (k : ∀ s', VChg [.v1, .v2, .v3, .v4] s s' →
      Lanes (s'.v .v2) (fun e => (A e + B e * Z e % 3329) % 3329) →
      Lanes (s'.v .v1) (fun e => (A e + (3329 - B e * Z e % 3329)) % 3329) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (vbfly z ++ rest)) s Q := by
  simp only [vbfly, List.append_assoc, List.cons_append]
  refine vmulq_ok (hc := hc) (hf := hB) (hf' := hB') (hg := hZ) (hg' := hZ')
    (k := fun s₁ h₁ l₁ => ?_)
  have c₁ := hc.chg h₁
  have t₁ : ∀ e < 4, B e * Z e % 3329 < 3329 := fun e _ => Nat.mod_lt _ (by decide)
  refine wp_vop (d := .v2) rfl fun s₂ h₂ => ?_
  have a₁ : Lanes (s₁.v .v0) A := by rw [h₁.get .v0]; exact hA
  have l₂ := lanes_add a₁ l₁
  rw [← h₂.v] at l₂
  refine vcsub_ok (by decide) (c₁.chg h₂.chg).q (f := fun e => (A e + B e * Z e % 3329) % 2 ^ 32) l₂ (fun e he => ?_) fun s₃ h₃ l₃ => ?_
  · have := hA' e he; have := t₁ e he; omega
  refine wp_vop (d := .v3) rfl fun s₄ h₄ => wp_vop (d := .v4) rfl fun s₅ h₅ => wp_vop (d := .v1) rfl
    fun s₆ h₆ => ?_
  have e0 : s₃.v .v0 = s.v .v0 := by rw [h₃.get .v0, h₂.get .v0, h₁.get .v0]
  have e1 : s₃.v .v1 = s₁.v .v1 := by rw [h₃.get .v1, h₂.get .v1]
  have a₃ : Lanes (s₃.v .v0) A := by rw [e0]; exact hA
  have b₃ : Lanes (s₃.v .v1) fun e => B e * Z e % 3329 := by rw [e1]; exact l₁
  have l₄ := lanes_sub a₃ b₃
  rw [← h₄.v] at l₄
  have l₅ := lanes_add l₄ (c₁.chg ((h₂.chg.trans h₃).trans h₄.chg)).q
  rw [← h₅.v] at l₅
  have a₅ : Lanes (s₅.v .v3) fun e => (2 ^ 32 - B e * Z e % 3329 + A e) % 2 ^ 32 := by
    rw [h₅.get .v3]; exact l₄
  have l₆ := lanes_umin a₅ l₅
  rw [← h₆.v] at l₆
  refine k s₆ (((((h₁.trans h₂.chg).trans h₃).trans h₄.chg).trans h₅.chg).trans h₆.chg |>.mono)
    (by rw [h₆.get .v2, h₅.get .v2, h₄.get .v2]
        exact l₃.congr fun e he => by
          show (A e + B e * Z e % 3329) % 2 ^ 32 % 3329 = _
          have := hA' e he; have := t₁ e he
          rw [Nat.mod_eq_of_lt (show A e + B e * Z e % 3329 < 2 ^ 32 by bdd_omega)])
    (l₆.congr fun e he => ?_)
  have := hA' e he; have := t₁ e he
  show min _ _ = _
  omega

/-- `vibfly z`: the butterflies of Algorithm 10 on the lanes of `v0` and `v1`. -/
theorem vibfly_ok {z : VReg} (hz : z ∉ [VReg.v0, .v1, .v2, .v3, .v4, .v16, .v17] := by decide)
    (hc : VConsts s) {A B Z : Nat → Nat} (hA : Lanes (s.v .v0) A) (hA' : ∀ e < 4, A e < 3329)
    (hB : Lanes (s.v .v1) B) (hB' : ∀ e < 4, B e < 3329) (hZ : Lanes (s.v z) Z)
    (hZ' : ∀ e < 4, Z e < 3329)
    (k : ∀ s', VChg [.v1, .v2, .v3] s s' →
      Lanes (s'.v .v2) (fun e => (A e + B e) % 3329) →
      Lanes (s'.v .v1) (fun e => (B e + (3329 - A e)) % 3329 * Z e % 3329) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (vibfly z ++ rest)) s Q := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  simp only [vibfly, List.append_assoc, List.cons_append]
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ := lanes_add hA hB
  rw [← h₁.v] at l₁
  refine vcsub_ok (by decide) (hc.chg h₁.chg).q (f := fun e => (A e + B e) % 2 ^ 32) l₁ (fun e he => ?_) fun s₂ h₂ l₂ => ?_
  · have := hA' e he; have := hB' e he; omega
  have c₂ := hc.chg (h₁.chg.trans h₂)
  refine wp_vop (d := .v1) rfl fun s₃ h₃ => wp_vop (d := .v3) rfl fun s₄ h₄ => wp_vop (d := .v1) rfl
    fun s₅ h₅ => ?_
  have e0 : s₂.v .v0 = s.v .v0 := by rw [h₂.get .v0, h₁.get .v0]
  have e1 : s₂.v .v1 = s.v .v1 := by rw [h₂.get .v1, h₁.get .v1]
  have a₂ : Lanes (s₂.v .v1) B := by rw [e1]; exact hB
  have b₂ : Lanes (s₂.v .v0) A := by rw [e0]; exact hA
  have l₃ := lanes_sub a₂ b₂
  rw [← h₃.v] at l₃
  have l₄ := lanes_add l₃ (c₂.chg h₃.chg).q
  rw [← h₄.v] at l₄
  have a₄ : Lanes (s₄.v .v1) fun e => (2 ^ 32 - A e + B e) % 2 ^ 32 := by
    rw [h₄.get .v1]; exact l₃
  have l₅ := lanes_umin a₄ l₄
  rw [← h₅.v] at l₅
  have c₅ := c₂.chg ((h₃.chg.trans h₄.chg).trans h₅.chg)
  have d₅ : ∀ e < 4, min ((2 ^ 32 - A e + B e) % 2 ^ 32) (((2 ^ 32 - A e + B e) % 2 ^ 32 + 3329) % 2 ^ 32) =
      (B e + (3329 - A e)) % 3329 := fun e he => by
    have := hA' e he; have := hB' e he; omega
  have z₅ : Lanes (s₅.v z) Z := by
    rw [h₅.get z hz.2.1, h₄.get z hz.2.2.2.1, h₃.get z hz.2.1, h₂.v z (by simp [hz.2.2.1, hz.2.2.2.1]),
      h₁.get z hz.2.2.1]
    exact hZ
  refine vmulq_ok (d := .v1) (z := z) (t := .v3) (hc := c₅) (hf := l₅.congr d₅)
    (hf' := fun e _ => Nat.mod_lt _ (by decide)) (hg := z₅) (hg' := hZ') (k := fun s₆ h₆ l₆ => ?_)
  refine k s₆ ((((h₁.chg.trans h₂).trans h₃.chg).trans h₄.chg).trans h₅.chg |>.trans h₆ |>.mono)
    (by rw [h₆.get .v2, h₅.get .v2, h₄.get .v2, h₃.get .v2]
        exact l₂.congr fun e he => by
          show (A e + B e) % 2 ^ 32 % 3329 = _
          have := hA' e he; have := hB' e he
          rw [Nat.mod_eq_of_lt (show A e + B e < 2 ^ 32 by bdd_omega)]) l₆

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

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.AddSub`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.NttVec`. -/
section

/-!
# ML-KEM on AArch64: polynomials in vectors

Four coefficients of a polynomial loaded into a vector (`lanes_load`) and two
vectors stored into it (`polyIs_write16x2`). The butterflies of a block of the
NTT and its inverse some at a time are in `Proof/MlKem/Ntt.lean`
(`nttBlockN_add`, `nttBlockN_get'`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.MlKem

theorem coeffAddr_off (p : Addr) (j k : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4 * k) = coeffAddr p (j + k) := by
  rw [coeffAddr, coeffAddr, ptr_add, Nat.mul_add]

/-- The 16 bytes at coefficient `j` of `P`, as lanes. -/
theorem lanes_load {m : Mem} {p : Addr} {P : Poly} (h : PolyIs m p P) {j : Nat} (hj : j + 4 ≤ 256) :
    Lanes (m.read (coeffAddr p j) 16) fun e => (P[j + e]!).val := fun e he => by
  rw [read16, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    rw [VG.Proof.MlKem.AArch64.coeffAddr_off, ← coeffAt_eq, polyIs_toNat h (show _ < n by rw [n_eq]; omega)]

/-- Coefficient `i` after storing the vector `x` at coefficient `j`. -/
theorem coeffAt_write16 (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.write (coeffAddr p j) 16 x) p i =
      if j ≤ i ∧ i < j + 4 then vword x (i - j) else coeffAt m p i := by
  rw [← ofVWords_vword x, VG.Proof.MlKem.AArch64.write16, show coeffAddr p j + BitVec.ofNat 64 4 = coeffAddr p (j + 1) from
      VG.Proof.MlKem.AArch64.coeffAddr_off p j 1, show coeffAddr p j + BitVec.ofNat 64 8 = coeffAddr p (j + 2) from
      VG.Proof.MlKem.AArch64.coeffAddr_off p j 2, show coeffAddr p j + BitVec.ofNat 64 12 = coeffAddr p (j + 3) from
      VG.Proof.MlKem.AArch64.coeffAddr_off p j 3]
  have hn : ∀ k, k < 4 → j + k < n := fun k hk => by rw [n_eq]; omega
  rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (hn 3 (by decide)),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (hn 2 (by decide)),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (hn 1 (by decide)),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show j < n by rw [n_eq]; omega)]
  rcases (by omega : i < j ∨ i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3 ∨ j + 4 ≤ i) with
    h | rfl | rfl | rfl | rfl | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, Nat.sub_self,
      Nat.add_sub_cancel_left, ofVWords_vword]

/-- Two vectors stored into a polynomial, with the lanes `a` and `b`. -/
theorem polyIs_write16x2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) (hsep : j + 4 ≤ j' ∨ j' + 4 ≤ j) {x y : BitVec 128}
    {a b : Nat → Zq} (hx : Lanes x fun e => (a e).val) (hy : Lanes y fun e => (b e).val)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 4 then a (i - j)
      else if j' ≤ i ∧ i < j' + 4 then b (i - j') else P[i]!) :
    PolyIs ((m.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) p R :=
  polyIs_of_toNat fun i hi => by
    rw [n_eq] at hi
    rw [VG.Proof.MlKem.AArch64.coeffAt_write16 _ _ hj' _ hi, VG.Proof.MlKem.AArch64.coeffAt_write16 _ _ hj _ hi, hR i hi]
    by_cases h1 : j' ≤ i ∧ i < j' + 4
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h1, hy _ (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j + 4
      · rw [ite_eq_left h2, ite_eq_left h2, hx _ (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, polyIs_toNat hP (by rw [n_eq]; exact hi)]

theorem frame16 {m m' : Mem} {p : Addr} (hf : Frame [polyRegion p] m m') {j : Nat} (hj : j + 4 ≤ 256)
    (x : BitVec 128) : Frame [polyRegion p] m (m'.write (coeffAddr p j) 16 x) :=
  hf.write (n := 16) (List.mem_singleton_self _) x (contains_off (by omega) (by decide))

theorem coeffAddr_step (p : Addr) (a : Nat) :
    coeffAddr p a + BitVec.ofNat 64 16 = coeffAddr p (a + 4) := by
  rw [coeffAddr, coeffAddr, ptr_add, show 4 * a + 16 = 4 * (a + 4) by omega]

theorem CoeffsUpTo.write16 {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : CoeffsUpTo m p t G old) (ht : t + 4 ≤ 256) {x : BitVec 128}
    (hx : ∀ e < 4, vword x e = G (t + e)) : CoeffsUpTo (m.write (coeffAddr p t) 16 x) p (t + 4) G old :=
  fun i hi => by
    rw [VG.Proof.MlKem.AArch64.coeffAt_write16 _ _ ht _ hi, h i hi]
    by_cases c : t ≤ i ∧ i < t + 4
    · rw [ite_eq_left c, ite_eq_left (by omega), hx _ (by omega), show t + (i - t) = i by omega]
    · rw [ite_eq_right c]
      by_cases c' : i < t
      · rw [ite_eq_left c', ite_eq_left (by omega)]
      · rw [ite_eq_right c', ite_eq_right (by omega)]

/-- The lanes of four coefficients, from their values. -/
theorem lanes_coeffs {m : Mem} {p : Addr} {j : Nat} {A : Nat → Nat}
    (h : ∀ e < 4, (coeffAt m p (j + e)).toNat = A e) : Lanes (m.read (coeffAddr p j) 16) A :=
  fun e he => by
    rw [read16, vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
      rw [VG.Proof.MlKem.AArch64.coeffAddr_off, ← coeffAt_eq] <;> exact h _ (by decide)

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.AddSub`. -/
section

/-!
# ML-KEM on AArch64: `vg_mlkem_add` and `vg_mlkem_sub`

Both are `mapLoop` around an arithmetic step; the loop is proven once for any
step that computes a function `F` of the two coefficients (`OpSpec`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem

/-- The contract the proofs are written against (and verified callers use);
the artifacts' are the shared contracts of `Spec/`, which imply it.
AArch64 contract for `f = x0, g = x1` (both `[u32; 256]`): if the
polynomials at `f` and `g` are reduced, `f` becomes `op (f, g)`, reduced.
The code may read `g` and read and write `f`, which do not overlap. -/
def accAArch64 (op : Poly → Poly → Poly) : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 1024⟩] ∧ s.wr = [⟨s.gpr .x0, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 1024⟩ ∧
    Reduced s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1)
  post s s' :=
    PolyIs s'.mem (s.gpr .x0) (op (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem

/-- `op` computes `F a b` in the lanes of `v2` from those of `v0 = a` and
`v1 = b`, with `q` in the lanes of `v16`, changing only `v2` and `v3`. -/
def VOpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (A B : Nat → Nat), (∀ e < 4, A e < q) →
    (∀ e < 4, B e < q) → Lanes (s.v .v0) A → Lanes (s.v .v1) B → Lanes (s.v .v16) (fun _ => 3329) →
    (∀ s', VChg [.v2, .v3] s s' → Lanes (s'.v .v2) (fun e => F (A e) (B e)) → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem vaddOp_spec : VG.Proof.MlKem.AArch64.VOpSpec vaddOp fun a b => condSub (a + b) := by
  intro is s Q A B hA hB lA lB hq k
  have q_ : q = 3329 := rfl
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ := lanes_add lA lB
  rw [← h₁.v] at l₁
  refine vcsub_ok (by decide) (by rw [h₁.get .v16]; exact hq) (f := fun e => (A e + B e) % 2 ^ 32) l₁
    (fun e he => by have := hA e he; have := hB e he; omega) fun s₂ h₂ l₂ =>
    k s₂ (h₁.chg.trans h₂ |>.mono) (l₂.congr fun e he => ?_)
  have := hA e he; have := hB e he
  simp only [condSub]; split <;> omega

theorem vsubOp_spec : VG.Proof.MlKem.AArch64.VOpSpec vsubOp fun a b => condSub (a + q - b) := by
  intro is s Q A B hA hB lA lB hq k
  have q_ : q = 3329 := rfl
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => wp_vop (d := .v3) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg |>.mono) ?_
  have l₁ := lanes_sub lA lB
  rw [← h₁.v] at l₁
  have q₁ : Lanes (s₁.v .v16) fun _ => 3329 := by rw [h₁.get .v16]; exact hq
  have l₂ := lanes_add l₁ q₁
  rw [← h₂.v] at l₂
  have a₂ : Lanes (s₂.v .v2) fun e => (2 ^ 32 - B e + A e) % 2 ^ 32 := by rw [h₂.get .v2]; exact l₁
  have l₃ := lanes_umin a₂ l₂
  rw [← h₃.v] at l₃
  refine l₃.congr fun e he => ?_
  have := hA e he; have := hB e he
  show min _ _ = _
  simp only [condSub]; split <;> omega

/-! ## The loop -/

section
variable (F : Nat → Nat → Nat) (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev gP : Addr := s₀.gpr .x1

/-- The new value of coefficient `i`. -/
def newC (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (F (coeffAt s₀.mem (VG.Proof.MlKem.AArch64.fP s₀) i).toNat (coeffAt s₀.mem (VG.Proof.MlKem.AArch64.gP s₀) i).toNat)

end

structure AccPre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem.AArch64.gP s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.AArch64.fP s₀)]
  disj : (polyRegion (VG.Proof.MlKem.AArch64.fP s₀)).Disjoint (polyRegion (VG.Proof.MlKem.AArch64.gP s₀))
  f : Reduced s₀.mem (VG.Proof.MlKem.AArch64.fP s₀)
  g : Reduced s₀.mem (VG.Proof.MlKem.AArch64.gP s₀)

/-- After `k` vectors of four coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = coeffAddr (VG.Proof.MlKem.AArch64.fP s₀) (4 * k)
  x1 : s.gpr .x1 = coeffAddr (VG.Proof.MlKem.AArch64.gP s₀) (4 * k)
  x10 : (s.gpr .x10).toNat = 64 - k
  q16 : Lanes (s.v .v16) fun _ => 3329
  f : CoeffsUpTo s.mem (VG.Proof.MlKem.AArch64.fP s₀) (4 * k) (VG.Proof.MlKem.AArch64.newC F s₀) (coeffAt s₀.mem (VG.Proof.MlKem.AArch64.fP s₀))
  g : ∀ i < 256, coeffAt s.mem (VG.Proof.MlKem.AArch64.gP s₀) i = coeffAt s₀.mem (VG.Proof.MlKem.AArch64.gP s₀) i

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlKem.AArch64.VOpSpec op F) {s₀ : State}
    (hp : VG.Proof.MlKem.AArch64.AccPre s₀) {k : Nat} (hk : k < 64) {s : State} (h : VG.Proof.MlKem.AArch64.MapInv F s₀ k s) :
    WP isa (.block (vmapBody op)) s fun s' =>
      VG.Proof.MlKem.AArch64.MapInv F s₀ (k + 1) s' ∧ ((s'.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 64) := by
  show WP isa (.block (.ldrq .v0 .x0 0 :: .ldrq .v1 .x1 0 :: (op ++
    (.strq .v2 .x0 0 :: (([.addImm .x .x0 .x0 16, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1] : List Instr) ++
      []))))) s _
  have hj : 4 * k + 4 ≤ 256 := by omega
  refine wp_ldrq (a := coeffAddr (VG.Proof.MlKem.AArch64.fP s₀) (4 * k)) (by decide) (by rw [h.x0, ptr_zero]) ?_
    fun s₁ h₁ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd_wr (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  refine wp_ldrq (a := coeffAddr (VG.Proof.MlKem.AArch64.gP s₀) (4 * k)) (by decide) (by rw [h₁.gpr, h.x1, ptr_zero]) ?_
    fun s₂ h₂ => ?_
  · rw [h₁.rd, h₁.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  have lA : Lanes (s₂.v .v0) fun e => (coeffAt s₀.mem (VG.Proof.MlKem.AArch64.fP s₀) (4 * k + e)).toNat := by
    rw [h₂.get .v0, h₁.v]
    exact VG.Proof.MlKem.AArch64.lanes_coeffs fun e he => by rw [h.f _ (by omega), ite_eq_right (by omega)]
  have lB : Lanes (s₂.v .v1) fun e => (coeffAt s₀.mem (VG.Proof.MlKem.AArch64.gP s₀) (4 * k + e)).toNat := by
    rw [h₂.v, h₁.mem]
    exact VG.Proof.MlKem.AArch64.lanes_coeffs fun e he => by rw [h.g _ (by omega)]
  have q₂ : Lanes (s₂.v .v16) fun _ => 3329 := by rw [h₂.get .v16, h₁.get .v16]; exact h.q16
  refine hop _ s₂ _ _ _ (fun e _ => hp.f _ (by rw [n_eq]; omega))
    (fun e _ => hp.g _ (by rw [n_eq]; omega)) lA lB q₂ fun s₃ h₃ l₃ => ?_
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_strq (a := coeffAddr (VG.Proof.MlKem.AArch64.fP s₀) (4 * k)) (by decide) (by rw [g₃, h.x0, ptr_zero]) ?_
    fun s₄ h₄ => ?_
  · rw [h₃.wr, h₂.wr, h₁.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x0, .x1, .x10] s₄ w' ∧ w'.mem = s₄.mem ∧
      w'.gpr .x0 = s₄.gpr .x0 + BitVec.ofNat 64 16 ∧ w'.gpr .x1 = s₄.gpr .x1 + BitVec.ofNat 64 16 ∧
      w'.gpr .x10 = s₄.gpr .x10 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
      wp_subImm (by decide) fun s₇ h₇ e₇ => wp_nil ⟨((h₅.keep.trans h₆.keep).trans h₇.keep).mono,
        by rw [h₇.mem, h₆.mem, h₅.mem], by rw [h₇.get .x0, h₆.get .x0, e₅],
        by rw [h₇.get .x1, e₆, h₅.get .x1], by rw [e₇, h₆.get .x10, h₅.get .x10]⟩))
    fun s' ⟨⟨k', m', e0, e1, e10⟩, hv⟩ => ?_
  have g₄ : s₄.gpr = s.gpr := by rw [h₄.gpr, g₃]
  have c10 : (s₄.gpr .x10).toNat = 64 - k := by rw [g₄, h.x10]
  have v10 : (s'.gpr .x10).toNat = 64 - (k + 1) := by
    rw [e10, toNat_sub_n (by rw [c10]; simp; omega), c10]; simp; omega
  have mm : s'.mem = s.mem.write (coeffAddr (VG.Proof.MlKem.AArch64.fP s₀) (4 * k)) 16 (s₃.v .v2) := by
    rw [m', h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have k₄ := ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans k')
  refine ⟨⟨by rw [k₄.rd, h.rd], by rw [k₄.wr, h.wr], by rw [k₄.sp, h.sp], ?_, ?_, v10, ?_, ?_,
    fun i hi => ?_⟩, by rw [v10]; omega⟩
  · rw [e0, g₄, h.x0, VG.Proof.MlKem.AArch64.coeffAddr_step, show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [e1, g₄, h.x1, VG.Proof.MlKem.AArch64.coeffAddr_step, show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [hv, h₄.v, h₃.get .v16, h₂.get .v16, h₁.get .v16]; exact h.q16
  · rw [mm, show 4 * (k + 1) = 4 * k + 4 by omega]
    refine CoeffsUpTo.write16 h.f hj fun e he => BitVec.eq_of_toNat_eq ?_
    rw [l₃ e he, VG.Proof.MlKem.AArch64.newC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (l₃.lt he)]
  · rw [mm, coeffAt_frame (VG.Proof.MlKem.AArch64.frame16 (Frame.refl _ _) hj _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.disj.symm) hi, h.g i hi]

theorem map_loop {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlKem.AArch64.VOpSpec op F) {s₀ : State}
    (hp : VG.Proof.MlKem.AArch64.AccPre s₀) : WP isa (vmapLoop op) s₀ (VG.Proof.MlKem.AArch64.MapInv F s₀ 64) := by
  refine WP.seq ?_
  show WP isa (.block ([Instr.movz .x .x9 3329 0] ++ (.vop (.dup .s4 .v16 .x9) ::
    (([.movz .x .x10 64 0] : List Instr) ++ [])))) s₀ _
  refine wp_scalar (by decide) (P := fun s₁ => Keep [.x9] s₀ s₁ ∧ s₁.mem = s₀.mem ∧
      (s₁.gpr .x9).toNat = 3329)
    (wp_movz fun s₁ h₁ e₁ => wp_nil ⟨h₁.keep, h₁.mem, by rw [e₁]; rfl⟩) fun s₁ ⟨k₁, m₁, e9⟩ _ => ?_
  refine wp_vop (d := .v16) rfl fun s₂ h₂ => ?_
  refine wp_scalar (by decide) (P := fun s₃ => Keep [.x10] s₂ s₃ ∧ s₃.mem = s₂.mem ∧
      (s₃.gpr .x10).toNat = 64)
    (wp_movz fun s₃ h₃ e₃ => wp_nil ⟨h₃.keep, h₃.mem, by rw [e₃]; rfl⟩) fun s₃ ⟨k₃, m₃, e10⟩ hv₃ =>
    wp_nil ?_
  refine count_loop (by decide) (VG.Proof.MlKem.AArch64.MapInv F s₀) (fun k hk s h => VG.Proof.MlKem.AArch64.map_step hop hp hk h) ?_
  have k₃ := (k₁.trans h₂.keep).trans k₃
  have m : s₃.mem = s₀.mem := by rw [m₃, h₂.mem, m₁]
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, coeffAddr]; exact (BitVec.add_zero _).symm,
    by rw [k₃.get .x1, coeffAddr]; exact (BitVec.add_zero _).symm, by rw [e10], ?_, fun i hi => ?_,
    fun i hi => by rw [m]⟩
  · rw [hv₃, h₂.v]
    exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e9]
  · rw [m, ite_eq_right (by omega)]

theorem map_correct {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlKem.AArch64.VOpSpec op F)
    {G : Poly → Poly → Poly}
    (hG : ∀ P R : Poly, ∀ i < n, ((G P R)[i]!).val = F (P[i]!).val (R[i]!).val)
    (hpres : (vmapLoop op).allInstrs (keeps (RegSet.ofList preserved)) = true)
    (s : State) (hs : (VG.Proof.MlKem.accAArch64 G).pre s)
    (hv : (vmapLoop op).allInstrs keepsV = true := by decide +kernel) :
    ∃ t s', Exec isa (vmapLoop op) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.accAArch64 G).post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hp : VG.Proof.MlKem.AArch64.AccPre s := ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨t, s', he, hI⟩ := VG.Proof.MlKem.AArch64.map_loop (F := F) hop hp
  refine ⟨t, s', he, abi_of rfl hpres he hv, ?_⟩
  show PolyIs s'.mem (VG.Proof.MlKem.AArch64.fP s) (G (polyAt s.mem (VG.Proof.MlKem.AArch64.fP s)) (polyAt s.mem (VG.Proof.MlKem.AArch64.gP s)))
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [hI.f i hi, ite_eq_left (by rw [n_eq] at hi; omega), VG.Proof.MlKem.AArch64.newC, hG _ _ i hi, polyAt_val hp.f hi,
    polyAt_val hp.g hi]

theorem map_ct {op : List Instr} {G : Poly → Poly → Poly}
    (h : (Taint.check taint (Taint.ofRegs [.x0, .x1]) (vmapLoop op)
      (Taint.hintOf taint (Taint.ofRegs [.x0, .x1]) (vmapLoop op))).isSome = true) :
    ConstantTime isa (VG.Proof.MlKem.accAArch64 G).pre (VG.Proof.MlKem.accAArch64 G).pub (vmapLoop op) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ h
  intro s₁ s₂ _ _ ⟨h0, h1, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

/-! ## `add` and `sub` -/

/-- A state satisfying the preconditions: two polynomials of zeros. -/
def accSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_correct : ∀ s, (VG.Proof.MlKem.accAArch64 Spec.MlKem.add).pre s →
    ∃ t s', Exec isa Impl.MlKem.AArch64.add s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.MlKem.accAArch64 Spec.MlKem.add).post s s' :=
  VG.Proof.MlKem.AArch64.map_correct VG.Proof.MlKem.AArch64.vaddOp_spec (fun P R i hi => by rw [add_get _ _ hi, val_add]) (by decide +kernel)

theorem sub_correct : ∀ s, (VG.Proof.MlKem.accAArch64 Spec.MlKem.sub).pre s →
    ∃ t s', Exec isa Impl.MlKem.AArch64.sub s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.MlKem.accAArch64 Spec.MlKem.sub).post s s' :=
  VG.Proof.MlKem.AArch64.map_correct VG.Proof.MlKem.AArch64.vsubOp_spec (fun P R i hi => by rw [sub_get _ _ hi, val_sub]) (by decide +kernel)

theorem add_verified :
    Verified AArch64.target Impl.MlKem.AArch64.add (Spec.MlKem.addContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlKem.AArch64.add_correct (VG.Proof.MlKem.AArch64.map_ct (by taint_decide)) (by
    mlkem_implies [Spec.MlKem.addContract, Spec.MlKem.accSig, VG.Proof.MlKem.accAArch64, AArch64.abi,
      AArch64.argRegs] [accSat] using VG.Proof.MlKem.AArch64.accSat)

theorem sub_verified :
    Verified AArch64.target Impl.MlKem.AArch64.sub (Spec.MlKem.subContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlKem.AArch64.sub_correct (VG.Proof.MlKem.AArch64.map_ct (by taint_decide)) (by
    mlkem_implies [Spec.MlKem.subContract, Spec.MlKem.accSig, VG.Proof.MlKem.accAArch64, AArch64.abi,
      AArch64.argRegs] [accSat] using VG.Proof.MlKem.AArch64.accSat)

end VG.Proof.MlKem.AArch64

end

end
