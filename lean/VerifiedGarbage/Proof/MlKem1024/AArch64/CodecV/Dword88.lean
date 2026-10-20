module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane

/-!
# ML-KEM-1024 on AArch64: groups of 88 bits

The two doublewords of a register, groups of 44 bits, as one group of 88 bits in its 11 low bytes
(`merge88_ok`): SHL by 44 and EXT by 8 bytes put the high group's low 20 bits above the low group,
ORR joins them, and INS puts the high group's high 24 bits in the second doubleword.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV

/-- EXT of a register with itself by eight bytes swaps its doublewords. -/
theorem vdword_ext8 (y : BitVec 128) {l : Nat} (hl : l < 2) :
    vdword (((y ++ y) >>> (8 * 8)).extractLsb' 0 128) l = vdword y (1 - l) := by
  rw [← Tbl.ofVDwords_halves y, ext8_pair]
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · rw [vdword_ofVDwords_0, vdword_ofVDwords_1]
  · rw [vdword_ofVDwords_1, vdword_ofVDwords_0]

theorem vdword_setLane64 (v : BitVec 128) {j e : Nat} (hj : j < 2) (he : e < 2) (x : BitVec 64) :
    vdword (setLane v 64 j x) e = if e = j then x else vdword v e := by
  have := extract_setLane64 v x hj he
  simp only [eq_comm (a := j)] at this
  exact this

/-- The bytes of a group of 88 bits, from its doublewords. -/
theorem bytes88 {g0 g1 : Nat} (h0 : g0 < 2 ^ 44) {j : Nat} (hj : j < 11) :
    (if j < 8 then (g0 + g1 % 2 ^ 20 * 2 ^ 44) / 2 ^ (8 * j) % 2 ^ 8
      else g1 / 2 ^ 20 / 2 ^ (8 * (j - 8)) % 2 ^ 8) = (g0 + g1 * 2 ^ 44) / 2 ^ (8 * j) % 2 ^ 8 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 by
    omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem merge88_ok {s : State} {v : VReg} (h19 : v ≠ .v19) (h23 : v ≠ .v23) {g : Nat → Nat}
    (hg : DLanes (s.v v) g) (hg0 : g 0 < 2 ^ 44) :
    WP isa (.block (merge88 v)) s fun t => VChg [.v23, .v19, v] s t ∧
      ∀ j < 11, (vbyte (t.v v) j).toNat = (g 0 + g 1 * 2 ^ 44) / 2 ^ (8 * j) % 2 ^ 8 := by
  unfold merge88
  refine wp_vop (eval_shift (by decide)) fun s1 h1 => wp_vop (eval_shift (by decide)) fun s2 h2 =>
    wp_vop (by simp only [VOp.eval]; rfl) fun s3 h3 => wp_vop rfl fun s4 h4 =>
    wp_vop (x := setLane (s4.v v) 64 1 (vdword (s4.v .v23) 1)) (by simp only [VOp.eval]; rfl)
      fun t h5 => wp_nil ⟨?_, ?_⟩
  · exact ((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (((h | h) | h) | h) | h <;> simp [h])
  have v1 : s1.v v = s.v v := h1.get v h23
  have v2 : s2.v v = s.v v := by rw [h2.get v h19, v1]
  have d23 : (vdword (s1.v .v23) 1).toNat = g 1 / 2 ^ 20 := by
    rw [h1.v, StraightV.vdword_map2 _ _ _ (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hg 1 (by decide)]
  have d19 : (vdword (s3.v .v19) 0).toNat = g 1 * 2 ^ 44 % 2 ^ 64 := by
    rw [h3.v, vdword_ext8 _ (by decide), h2.v, StraightV.vdword_map2 _ _ _ (by decide)]
    simp only [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [v1, hg 1 (by decide)]
  have d40 : (vdword (s4.v v) 0).toNat = g 0 + g 1 % 2 ^ 20 * 2 ^ 44 := by
    rw [h4.v, StraightV.vdword_or, BitVec.toNat_or, h3.get v h19, v2, hg 0 (by decide), d19]
    have e : g 1 * 2 ^ 44 % 2 ^ 64 = g 1 % 2 ^ 20 * 2 ^ 44 := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 20 * 2 ^ 44 from by rw [← Nat.pow_add], Nat.mul_mod_mul_right]
    rw [e, or_shift hg0]
  have dt0 : (vdword (t.v v) 0).toNat = g 0 + g 1 % 2 ^ 20 * 2 ^ 44 := by
    rw [h5.v, vdword_setLane64 _ (by decide) (by decide)]; exact d40
  have dt1 : (vdword (t.v v) 1).toNat = g 1 / 2 ^ 20 := by
    rw [h5.v, vdword_setLane64 _ (by decide) (by decide), ite_eq_left rfl, h4.get .v23 (Ne.symm h23),
      h3.get .v23 (by decide), h2.get .v23 (by decide)]
    exact d23
  intro j hj
  rw [← bytes88 hg0 hj]
  by_cases h8 : j < 8
  · have e := toNat_vbyte_dword (t.v v) (l := 0) h8
    simp only [Nat.mul_zero, Nat.zero_add] at e
    rw [ite_eq_left h8, e, dt0]
  · have e := toNat_vbyte_dword (t.v v) (l := 1) (b := j - 8) (by omega)
    rw [show 8 * 1 + (j - 8) = j by omega] at e
    rw [ite_eq_right h8, e, dt1]

/-- TBL of `len` registers from `n`, at an index in the table. -/
theorem vbyte_tblN {s : State} {n m d : VReg} {len i k : Nat} (hi : i < 16)
    (hk : (vbyte (s.v m) i).toNat = k) (hk' : k < 16 * len) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * len then tableByte s.v n (vbyte (s.v m) i).toNat
      else if false then vbyte (s.v d) i else 0) i = tableByte s.v n k := by
  rw [vbyte_ofVBytes _ hi, hk, ite_eq_left hk']

/-- TBL of `len` registers from `n`, at an index past the table. -/
theorem vbyte_tblN_out {s : State} {n m d : VReg} {len i k : Nat} (hi : i < 16)
    (hk : (vbyte (s.v m) i).toNat = k) (hk' : 16 * len ≤ k) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * len then tableByte s.v n (vbyte (s.v m) i).toNat
      else if false then vbyte (s.v d) i else 0) i = 0 := by
  rw [vbyte_ofVBytes _ hi, hk, ite_eq_right (by omega)]; rfl

/-- ZIP1 of doublewords: the low doublewords of `x` and `y`. -/
theorem eval_zip1_d2 (x y : BitVec 128) : VPermOp.eval .zip1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) := by
  have sw : ∀ w : BitVec 64, (w.setWidth 128).setWidth 64 = w := fun w => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceDiv]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ, sw]

end VG.Proof.MlKem1024.AArch64.CodecV
