module

public import VerifiedGarbage.Impl.Bignum.Arm.RowStep
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The memory and arithmetic effects of one ARMv7 Montgomery row step -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest Upd mask16 wp_ldr wp_str toNat_shl toNat_shr toNat_and_mask16
  toNat_mul_lt)

theorem rowHalves_ok (s : State) :
    WP isa (.block rowHalves) s fun t =>
      t.gpr .r6 = s.gpr .r2 >>> 16 ∧ t.gpr .r2 = s.gpr .r2 &&& s.gpr .r9 ∧
      Preserves [.r2, .r6] s t := by
  apply WP.of_runBlock
  simp only [rowHalves, runBlock_cons, isa, exec, Op2.eval]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem rowPartials_ok (s : State) :
    WP isa (.block rowPartials) s fun t =>
      t.gpr .r3 = s.gpr .r1 * s.gpr .r2 ∧ t.gpr .r5 = s.gpr .r10 * s.gpr .r2 ∧
      t.gpr .r7 = s.gpr .r1 * s.gpr .r6 ∧ t.gpr .r4 = s.gpr .r10 * s.gpr .r6 ∧
      Preserves [.r3, .r4, .r5, .r7] s t := by
  apply WP.of_runBlock
  simp only [rowPartials, runBlock_cons, runStep_some, isa, exec, gpr_setReg, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

/-- The high word receives the cross product's high half and the carry of
its low half into the low word. -/
theorem add_cross_value (lo hi m : BitVec 32)
    (h : lo.toNat + hi.toNat * 2 ^ 32 + m.toNat * 2 ^ 16 < 2 ^ 64) :
    (lo + (m <<< 16)).toNat +
      (hi + (m >>> 16) + (if 2 ^ 32 ≤ lo.toNat + (m <<< 16).toNat then 1 else 0 : BitVec 32)).toNat *
        2 ^ 32 = lo.toNat + hi.toNat * 2 ^ 32 + m.toNat * 2 ^ 16 := by
  have hl := lo.isLt
  have hh := hi.isLt
  have hm := m.isLt
  have shl := toNat_shl m 16
  have shr := toNat_shr m 16
  by_cases hc : 2 ^ 32 ≤ lo.toNat + (m <<< 16).toNat
  · simp only [hc, ite_true, BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · simp only [hc, ite_false, BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-- `addCross r`: `r4:r3 += 2¹⁶ r`, exactly. -/
theorem addCross_ok (s : State) (r : Reg) (h3 : r ≠ .r3)
    (h : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr r).toNat * 2 ^ 16 < 2 ^ 64) :
    WP isa (.block (addCross r)) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr r).toNat * 2 ^ 16 ∧
      MacFrame [.r3, .r4] s t := by
  let f := addFlags s (s.gpr .r3) (s.gpr r <<< 16)
  let t := (f.setReg .r3 (s.gpr .r3 + (s.gpr r <<< 16))).setReg .r4
    (s.gpr .r4 + (s.gpr r >>> 16) +
      (if 2 ^ 32 ≤ (s.gpr .r3).toNat + (s.gpr r <<< 16).toNat then 1 else 0))
  have hsh : (1 ≤ 16 ∧ 16 ≤ 31) = True := by decide
  refine WP.of_runBlock ⟨t, ?_, ?_, ?_⟩
  · simp only [addCross, runBlock_cons, exec, Op2.eval, hsh, ↓reduceIte, Option.map_some,
      runStep_some, runBlock_nil, gpr_setReg, reduceCtorEq, c_setReg, h3]
    dsimp only [addFlags]
    simp only [decide_eq_true_eq]
    rfl
  · exact add_cross_value _ _ _ h
  · apply MacFrame.setReg (hr := by simp)
    apply MacFrame.setReg (hr := by simp)
    exact MacFrame.addFlags _ _ _ _

/-- `addCarry`: `r11:r3 := r4:r3 + r11`, exactly. -/
theorem addCarry_ok (s : State)
    (h : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr .r11).toNat < 2 ^ 64) :
    WP isa (.block addCarry) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr .r11).toNat ∧
      MacFrame [.r3, .r11] s t := by
  let f := addFlags s (s.gpr .r3) (s.gpr .r11)
  let t := (f.setReg .r3 (s.gpr .r3 + s.gpr .r11)).setReg .r11
    (s.gpr .r4 + (if 2 ^ 32 ≤ (s.gpr .r3).toNat + (s.gpr .r11).toNat then 1 else 0))
  refine WP.of_runBlock ⟨t, ?_, ?_, ?_⟩
  · simp only [addCarry, runBlock_cons, exec, Op2.eval, Option.map_some,
      show encodable (0 : BitVec 32) = true from rfl, ↓reduceIte, runStep_some, runBlock_nil,
      gpr_setReg, reduceCtorEq, c_setReg]
    dsimp only [addFlags]
    have hz (x : BitVec 32) : x + (0 : BitVec 32) = x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      change x.toNat % 2 ^ 32 = x.toNat
      exact Nat.mod_eq_of_lt x.isLt
    simp only [decide_eq_true_eq, hz]
    rfl
  · change ((s.gpr .r3 + s.gpr .r11).toNat +
      (s.gpr .r4 + (if 2 ^ 32 ≤ (s.gpr .r3).toNat + (s.gpr .r11).toNat then 1 else 0)).toNat * 2 ^ 32 = _)
    exact add_word_value _ _ _ h
  · apply MacFrame.setReg (hr := by simp)
    apply MacFrame.setReg (hr := by simp)
    exact MacFrame.addFlags _ _ _ _

/-- The four partial products of 16-bit halves sum to the full product. -/
theorem partials_value (x y : BitVec 32) :
    (x.toNat % 65536) * (y.toNat % 65536) + (x.toNat / 65536) * (y.toNat / 65536) * 2 ^ 32 +
      (x.toNat / 65536) * (y.toNat % 65536) * 2 ^ 16 + (x.toNat % 65536) * (y.toNat / 65536) * 2 ^ 16 =
        x.toNat * y.toNat := by
  have hx : x.toNat = x.toNat % 65536 + x.toNat / 65536 * 65536 := by omega
  have hy : y.toNat = y.toNat % 65536 + y.toNat / 65536 * 65536 := by omega
  generalize x.toNat % 65536 = a0 at hx ⊢
  generalize x.toNat / 65536 = a1 at hx ⊢
  generalize y.toNat % 65536 = b0 at hy ⊢
  generalize y.toNat / 65536 = b1 at hy ⊢
  rw [hx, hy]
  grind

/-- The product of the scalar `x`, held as its halves in `r1` and `r10`, and
the input word in `r2`. -/
theorem rowProduct_ok (s : State) (x : BitVec 32)
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16) :
    WP isa (.block rowProduct) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 = x.toNat * (s.gpr .r2).toNat ∧
      MacFrame [.r2, .r3, .r4, .r5, .r6, .r7, .r8] s t := by
  rw [rowProduct, List.append_assoc, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (rowHalves_ok s) ?_
  rintro s1 ⟨b1, b0, frame1⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (rowPartials_ok s1) ?_
  rintro s2 ⟨p00, p10, p01, p11, frame2⟩
  let y := s.gpr .r2
  have ha0 : (s2.gpr .r1).toNat = x.toNat % 65536 := by
    rw [frame2.regs .r1 (by simp), frame1.regs .r1 (by simp), h1, toNat_and_mask16]
  have ha1 : (s2.gpr .r10).toNat = x.toNat / 65536 := by
    rw [frame2.regs .r10 (by simp), frame1.regs .r10 (by simp), h10, toNat_shr]
  have hb0 : (s1.gpr .r2).toNat = y.toNat % 65536 := by
    rw [b0, h9, toNat_and_mask16]
  have hb1 : (s1.gpr .r6).toNat = y.toNat / 65536 := by rw [b1, toNat_shr]
  have hx := x.isLt
  have hy := y.isLt
  have lt (a b : Nat) (ha : a < 65536) (hb : b < 65536) : a * b < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)) (by decide)
  have v00 : (s2.gpr .r3).toNat = x.toNat % 65536 * (y.toNat % 65536) := by
    rw [p00, frame1.regs .r1 (by simp), toNat_mul_lt] <;>
      rw [← frame1.regs .r1 (by simp), ← frame2.regs .r1 (by simp), ha0, hb0]
    exact lt _ _ (by omega) (by omega)
  have v10 : (s2.gpr .r5).toNat = x.toNat / 65536 * (y.toNat % 65536) := by
    rw [p10, frame1.regs .r10 (by simp), toNat_mul_lt] <;>
      rw [← frame1.regs .r10 (by simp), ← frame2.regs .r10 (by simp), ha1, hb0]
    exact lt _ _ (by omega) (by omega)
  have v01 : (s2.gpr .r7).toNat = x.toNat % 65536 * (y.toNat / 65536) := by
    rw [p01, frame1.regs .r1 (by simp), toNat_mul_lt] <;>
      rw [← frame1.regs .r1 (by simp), ← frame2.regs .r1 (by simp), ha0, hb1]
    exact lt _ _ (by omega) (by omega)
  have v11 : (s2.gpr .r4).toNat = x.toNat / 65536 * (y.toNat / 65536) := by
    rw [p11, frame1.regs .r10 (by simp), toNat_mul_lt] <;>
      rw [← frame1.regs .r10 (by simp), ← frame2.regs .r10 (by simp), ha1, hb1]
    exact lt _ _ (by omega) (by omega)
  have total := partials_value x y
  have bound : x.toNat * y.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)) (by decide)
  apply WP.block_append_iff.mpr
  refine WP.mono (addCross_ok s2 .r5 (by decide)
    (by rw [v00, v11, v10]; omega)) ?_
  rintro s3 ⟨sum3, frame3⟩
  have r7 : (s3.gpr .r7).toNat = x.toNat % 65536 * (y.toNat / 65536) := by
    rw [frame3.regs .r7 (by simp), v01]
  refine WP.mono (addCross_ok s3 .r7 (by decide)
    (by rw [sum3, v00, v11, v10, r7]; omega)) ?_
  rintro s4 ⟨sum4, frame4⟩
  refine ⟨?_, ?_⟩
  · rw [sum4, sum3, v00, v11, v10, r7]
    omega
  · refine (frame1.macFrame.mono ?_).trans ((frame2.macFrame.mono ?_).trans
      ((frame3.mono ?_).trans (frame4.mono ?_)))
    all_goals intro r hr; cases r <;> simp_all

abbrev rowClobbers : List Reg := [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r11]

/-- A row step writes exactly one accumulator word. Its high word is the
carry for the next step; the accumulator and input addresses, and the
scalar's halves, stay fixed. -/
theorem rowStepAt_ok (s : State) (k : Nat) (hk : k < 4096) (a b : Addr) (x : BitVec 32)
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 k) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 k) = b)
    (hread : InRegions (s.rd ++ s.wr) b 4) (hwrite : InRegions s.wr a 4) :
    WP isa (rowStepAt k) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        x.toNat * (s.mem.readW b 32).toNat +
          (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧ Rest rowClobbers s t := by
  rw [rowStepAt, WP.seq_iff]
  refine wp_ldr hk hb hread fun s1 u1 => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (rowProduct_ok s1 x (by rw [u1.other .r1 (by decide), h1])
    (by rw [u1.other .r10 (by decide), h10]) (by rw [u1.other .r9 (by decide), h9])) ?_
  rintro s2 ⟨prod, frame2⟩
  have ptr2 : s2.gpr .r0 = s.gpr .r0 :=
    (frame2.regs .r0 (by simp)).trans (u1.other .r0 (by decide))
  rw [WP.seq_iff]
  refine wp_ldr (a := a) hk (by rw [ptr2]; exact ha)
    (by
      rw [frame2.rd, frame2.wr, u1.rd, u1.wr]
      rcases hwrite with ⟨R, hR, haR⟩
      exact ⟨R, List.mem_append_right _ hR, haR⟩) fun s3 u3 => WP.block_nil ?_
  have mem3 : s3.mem = s.mem := u3.mem.trans (frame2.mem.trans u1.mem)
  have acc3 : s3.gpr .r5 = s.mem.readW a 32 := by rw [u3.gpr, frame2.mem, u1.mem]
  have carry3 : s3.gpr .r11 = s.gpr .r11 :=
    (u3.other .r11 (by decide)).trans ((frame2.regs .r11 (by simp)).trans (u1.other .r11 (by decide)))
  have prod3 : (s3.gpr .r3).toNat + (s3.gpr .r4).toNat * 2 ^ 32 =
      x.toNat * (s.mem.readW b 32).toNat := by
    rw [u3.other .r3 (by decide), u3.other .r4 (by decide), prod, u1.gpr]
  have hb := mac_bound x (s.mem.readW b 32) (s.mem.readW a 32) (s.gpr .r11)
  rw [WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (addWord_ok s3 .r5 (by rw [prod3, acc3]; omega)) ?_
  rintro s4 ⟨sum4, frame4⟩
  have carry4 : s4.gpr .r11 = s.gpr .r11 := (frame4.regs .r11 (by simp)).trans carry3
  refine WP.mono (addCarry_ok s4 (by rw [sum4, prod3, acc3, carry4]; exact hb)) ?_
  rintro s5 ⟨sum5, frame5⟩
  have ptr5 : s5.gpr .r0 = s.gpr .r0 :=
    (frame5.regs .r0 (by simp)).trans ((frame4.regs .r0 (by simp)).trans
      ((u3.other .r0 (by decide)).trans ptr2))
  refine wp_str (a := a) hk (by rw [ptr5]; exact ha)
    (by rw [frame5.wr, frame4.wr, u3.wr, frame2.wr, u1.wr]; exact hwrite) fun s6 u6 => WP.block_nil ?_
  have out6 : s6.gpr .r3 = s5.gpr .r3 := congrFun u6.gpr .r3
  have carry6 : s6.gpr .r11 = s5.gpr .r11 := congrFun u6.gpr .r11
  refine ⟨?_, ?_, ?_⟩
  · rw [out6, carry6, sum5, sum4, prod3, acc3, carry4]
  · rw [u6.mem, frame5.mem, frame4.mem, mem3, out6]
  · have r2 : Rest rowClobbers s1 s2 := ⟨fun r hr => frame2.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h | h | h | h <;> simp [h]), frame2.rd, frame2.wr, frame2.sp⟩
    have r4 : Rest rowClobbers s3 s4 := ⟨fun r hr => frame4.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]), frame4.rd, frame4.wr, frame4.sp⟩
    have r5 : Rest rowClobbers s4 s5 := ⟨fun r hr => frame5.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]), frame5.rd, frame5.wr, frame5.sp⟩
    exact (u1.rest (by simp)).trans (r2.trans ((u3.rest (by simp)).trans (r4.trans (r5.trans
      (u6.rest _)))))

/-- The step at the pointers themselves. -/
theorem rowStep_ok (s : State) (a b : Addr) (x : BitVec 32)
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = b)
    (hread : InRegions (s.rd ++ s.wr) b 4) (hwrite : InRegions s.wr a 4) :
    WP isa rowStep s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        x.toNat * (s.mem.readW b 32).toNat +
          (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧ Rest rowClobbers s t :=
  rowStepAt_ok s 0 (by decide) a b x h1 h10 h9 ha hb hread hwrite

end VG.Proof.Bignum.Arm
