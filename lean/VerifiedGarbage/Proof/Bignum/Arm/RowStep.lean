module

public import VerifiedGarbage.Impl.Bignum.Arm.RowStep
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # The memory and arithmetic effects of one ARMv7 Montgomery row step -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest Upd mask16 wp_ldr wp_str wp_mov op2_reg)

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

theorem rowLow_ok (s : State) :
    WP isa (.block rowLow) s fun t =>
      t.gpr .r7 = s.gpr .r1 * s.gpr .r2 ∧
      t.gpr .r8 = s.gpr .r10 * s.gpr .r2 + ((s.gpr .r1 * s.gpr .r2) >>> 16) ∧
      Preserves [.r7, .r8] s t := by
  apply WP.of_runBlock
  simp only [rowLow, runBlock_cons, runStep_some, isa, exec,
    Op2.eval, gpr_setReg, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem rowCross_ok (s : State) :
    WP isa (.block rowCross) s fun t =>
      t.gpr .r4 = s.gpr .r10 * s.gpr .r6 + (s.gpr .r8 >>> 16) ∧
      t.gpr .r3 = s.gpr .r1 * s.gpr .r6 + (s.gpr .r8 &&& s.gpr .r9) ∧
      Preserves [.r3, .r4, .r5] s t := by
  apply WP.of_runBlock
  simp only [rowCross, runBlock_cons, runStep_some, isa, exec,
    Op2.eval, Option.map_some, gpr_setReg, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

/-- The product of the scalar `x`, held as its halves in `r1` and `r10`, and
the input word in `r2`: `wideMul`'s value, with the scalar split once. -/
theorem rowProduct_ok (s : State) (x : BitVec 32)
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16) :
    WP isa (.block rowProduct) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 = x.toNat * (s.gpr .r2).toNat ∧
      Preserves [.r2, .r3, .r4, .r5, .r6, .r7, .r8] s t := by
  rw [rowProduct, List.append_assoc, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (rowHalves_ok s) ?_
  rintro s1 ⟨b1, b0, frame1⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (rowLow_ok s1) ?_
  rintro s2 ⟨p, cross, frame2⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (rowCross_ok s2) ?_
  rintro s3 ⟨hi, mid, frame3⟩
  refine WP.mono (packProduct_ok s3) ?_
  rintro s4 ⟨hi4, lo4, frame4⟩
  refine ⟨?_, (frame1.mono ?_).trans ((frame2.mono ?_).trans ((frame3.mono ?_).trans (frame4.mono ?_)))⟩
  · rw [lo4, hi4, hi, mid, frame3.regs .r7 (by simp), frame3.regs .r9 (by simp),
      frame2.regs .r1 (by simp), frame2.regs .r10 (by simp),
      frame2.regs .r6 (by simp), frame2.regs .r9 (by simp), p, cross,
      frame1.regs .r1 (by simp), frame1.regs .r10 (by simp), frame1.regs .r9 (by simp), b0, b1,
      h1, h10, h9]
    exact wide_value _ _
  all_goals intro r hr; cases r <;> simp_all

abbrev rowClobbers : List Reg := [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r11]

/-- A row step writes exactly one accumulator word. Its high word is the
carry for the next step; the accumulator and input addresses, and the
scalar's halves, stay fixed. -/
theorem rowStep_ok (s : State) (a b : Addr) (x : BitVec 32)
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = b)
    (hread : InRegions (s.rd ++ s.wr) b 4) (hwrite : InRegions s.wr a 4) :
    WP isa rowStep s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        x.toNat * (s.mem.readW b 32).toNat +
          (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧ Rest rowClobbers s t := by
  rw [rowStep, WP.seq_iff]
  refine wp_ldr (by decide) hb hread fun s1 u1 => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (rowProduct_ok s1 x (by rw [u1.other .r1 (by decide), h1])
    (by rw [u1.other .r10 (by decide), h10]) (by rw [u1.other .r9 (by decide), h9])) ?_
  rintro s2 ⟨prod, frame2⟩
  have ptr2 : s2.gpr .r0 = s.gpr .r0 :=
    (frame2.regs .r0 (by simp)).trans (u1.other .r0 (by decide))
  rw [WP.seq_iff]
  refine wp_ldr (a := a) (by decide) (by rw [ptr2]; exact ha)
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
  refine WP.mono (addWord_ok s4 .r11 (by rw [sum4, prod3, acc3, carry4]; exact hb)) ?_
  rintro s5 ⟨sum5, frame5⟩
  have ptr5 : s5.gpr .r0 = s.gpr .r0 :=
    (frame5.regs .r0 (by simp)).trans ((frame4.regs .r0 (by simp)).trans
      ((u3.other .r0 (by decide)).trans ptr2))
  refine wp_str (a := a) (by decide) (by rw [ptr5]; exact ha)
    (by rw [frame5.wr, frame4.wr, u3.wr, frame2.wr, u1.wr]; exact hwrite) fun s6 u6 => ?_
  refine wp_mov (op2_reg _ _) fun s7 u7 => WP.block_nil ?_
  have out7 : s7.gpr .r3 = s5.gpr .r3 :=
    (u7.other .r3 (by decide)).trans (congrFun u6.gpr .r3)
  have carry7 : s7.gpr .r11 = s5.gpr .r4 := u7.gpr.trans (congrFun u6.gpr .r4)
  refine ⟨?_, ?_, ?_⟩
  · rw [out7, carry7, sum5, sum4, prod3, acc3, carry4]
  · rw [u7.mem, u6.mem, frame5.mem, frame4.mem, mem3, out7]
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
      ((u6.rest _).trans (u7.rest (by simp)))))))

end VG.Proof.Bignum.Arm
