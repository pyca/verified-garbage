module

public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Env
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Head
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Formula
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Formula
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # One iteration of the `_alt` ladder -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519 VG.Proof.Ed25519.AArch64
open VG.Proof.X25519.AArch64.Alt (AltOp altClob)
open VG.Proof.X25519.AArch64.Word (LoopKeep Good Scratch bitOffset)
open VG.Impl.Ed25519.AArch64 (offset)
open VG.Impl.X25519.AArch64.Alt

/-- The slots of the ladder's points, below `2·p` between iterations. -/
def S14 : VG.Impl.Ed25519.AArch64.Slot → Bool := fun i => decide (1 ≤ i.val ∧ i.val ≤ 4)

theorem altClob_sub : ∀ r ∈ altClob, r ∈ clob := by decide

theorem AltOp.lk {base : Addr} {o : VG.Impl.Ed25519.AArch64.Slot} {s t : State} (h : AltOp base (offset o) s t)
    (h1 : 1 ≤ o.val) : LoopKeep base s t :=
  ⟨fun r hr _ => h.gpr r (fun hm => hr (altClob_sub r hm)), h.rd, h.wr, h.sp,
    h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩

/-- A slot the operation does not write. -/
theorem fr {base : Addr} {o : VG.Impl.Ed25519.AArch64.Slot} {s t : State} (h : AltOp base (offset o) s t) (i : VG.Impl.Ed25519.AArch64.Slot)
    (hi : i ≠ o) : fe t.mem base (offset i) = fe s.mem base (offset i) :=
  h.mem.fe (apart i o hi) (by simp only [offset]; omega)

theorem x17_ok (s : State) :
    WP isa (.block [.movz .x .x17 0 0]) s fun t => t.gpr .x17 = 0 ∧ Keeps [.x17] s t := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr =>
    RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩

/-- `d = n` (`add d, n, #0`). -/
theorem mov_ok (s : State) (d n : Reg) :
    WP isa (.block [VG.Impl.Ed25519.AArch64.mov d n]) s fun t => t.gpr d = s.gpr n ∧
      Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 0) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

theorem cmaddA24_ok {base : Addr} {s : State} (hs : Scratch s base) (hz : s.gpr .x17 = 0) :
    WP isa (.block (VG.Impl.X25519.AArch64.AltLadder.cmaddA24 (offset 2) (offset 7) (offset 8))) s
      fun t => LoopKeep base s t ∧ t.gpr .x17 = 0 ∧ t.gpr .x19 = s.gpr .x19 ∧
        fe t.mem base (offset 2) < P2 ∧ Outside base (offset 2) 32 s.mem t.mem ∧
        env t.mem base = Function.update (env s.mem base) 2
          (toFe 121666 * env s.mem base 7 + env s.mem base 8) := by
  rw [VG.Impl.X25519.AArch64.AltLadder.cmaddA24, List.append_assoc, WP.block_append_iff]
  have ha : WP isa (.block [VG.Impl.Ed25519.AArch64.mov .x20 .x1, .movz .x .x1 0xdb42 0,
      .movk .x .x1 1 1]) s fun t => t.gpr .x20 = s.gpr .x1 ∧ (t.gpr .x1).toNat = 121666 ∧
      Keeps [.x20, .x1] s t := by
    apply WP.of_runBlock
    simp only [VG.Impl.Ed25519.AArch64.mov, runBlock_cons, runStep_some, runBlock_nil,
      exec_addImm_x (imm := 0) (by decide), VG.Proof.X25519.AArch64.exec_movz,
      VG.Proof.X25519.AArch64.exec_movk1, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [State.read, BitVec.setWidth_eq, BitVec.add_zero]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  refine WP.mono ha fun a ⟨a20, a1, ka⟩ => ?_
  have hsa : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmaddE hsa 2 7 8 (by decide) (by decide) (by decide)
    ((ka.gpr _ (by decide)).trans hz) a1) fun b ⟨hb, lb, eb⟩ => ?_
  refine WP.mono (mov_ok b .x1 .x20) fun t ⟨t1, kt⟩ => ?_
  have k1 : ∀ r, r ≠ .x1 → t.gpr r = b.gpr r := fun r hr =>
    kt.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr)
  refine ⟨⟨fun r hr h19 => ?_, by rw [kt.rd, hb.rd, ka.rd], by rw [kt.wr, hb.wr, ka.wr],
      by rw [kt.sp, hb.sp, ka.sp], ?_⟩, ?_, ?_, by rw [kt.mem]; exact lb,
    by rw [kt.mem, ← ka.mem]; exact hb.mem, by rw [kt.mem, eb, ka.mem]⟩
  · by_cases e1 : r = .x1
    · subst e1
      rw [t1, hb.gpr _ (by decide), a20]
    · have r20 : r ≠ .x20 := fun e => hr (e ▸ by decide)
      rw [k1 r e1, hb.gpr r (fun hm => hr (altClob_sub r hm)),
        ka.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨r20, e1⟩)]
  · rw [kt.mem, ← ka.mem]
    exact hb.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)
  · rw [k1 _ (by decide), hb.gpr _ (by decide), ka.gpr _ (by decide), hz]
  · rw [k1 _ (by decide), hb.gpr _ (by decide), ka.gpr _ (by decide)]

theorem AltOp.w768 {base : Addr} {o : VG.Impl.Ed25519.AArch64.Slot} {s t : State} (h : AltOp base (offset o) s t) :
    word t.mem base 768 = word s.mem base 768 :=
  h.mem.word (Or.inr (by simp only [offset]; omega)) (by decide)

theorem S14_cases : ∀ i : VG.Impl.Ed25519.AArch64.Slot, S14 i = true → i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide

theorem body_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} {st : Ladder} {i : Nat}
    (hs : Scratch s base) (hi : i < 255) (hg : Good (env s.mem base) x1 st)
    (hsw : st.swap ≤ 1) (hcnt : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hw : word s.mem base 768 = BitVec.ofNat 64 st.swap)
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i))
    (hB : Bel s.mem base S14) :
    WP isa (.block VG.Impl.X25519.AArch64.AltLadder.body) s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderStep k x1 st i) ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ word t.mem base 768 = BitVec.ofNat 64 (bit k i) ∧
      Bel t.mem base S14 := by
  simp only [VG.Impl.X25519.AArch64.AltLadder.body, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (x17_ok s) fun a ⟨za, ka⟩ => ?_
  have lka : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  have B : ∀ j : VG.Impl.Ed25519.AArch64.Slot, S14 j = true → fe a.mem base (offset j) < P2 := fun j hj => by
    rw [ka.mem]; exact hB j hj
  -- the sums and differences
  rw [WP.block_append_iff]
  refine WP.mono (subE (lka.scratch hs) 6 3 4 (by decide) (by decide) (by decide) za (B 4 rfl))
    fun b1 ⟨h1, e1⟩ => ?_
  have lk1 := lka.trans (AltOp.lk h1 (by decide))
  have z1 : b1.gpr .x17 = 0 := (h1.gpr _ (by decide)).trans za
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk1.scratch hs) 5 1 2 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 1 (by decide)]; exact B 1 rfl) (by rw [fr h1 2 (by decide)]; exact B 2 rfl))
    fun b2 ⟨h2, e2⟩ => ?_
  have lk2 := lk1.trans (AltOp.lk h2 (by decide))
  have z2 : b2.gpr .x17 = 0 := (h2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk2.scratch hs) 2 1 2 (by decide) (by decide) (by decide) z2
    (by rw [fr h2 2 (by decide), fr h1 2 (by decide)]; exact B 2 rfl))
    fun b3 ⟨h3, e3⟩ => ?_
  have lk3 := lk2.trans (AltOp.lk h3 (by decide))
  have z3 : b3.gpr .x17 = 0 := (h3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk3.scratch hs) 4 3 4 (by decide) (by decide) (by decide) z3
    (by rw [fr h3 3 (by decide), fr h2 3 (by decide), fr h1 3 (by decide)]; exact B 3 rfl)
    (by rw [fr h3 4 (by decide), fr h2 4 (by decide), fr h1 4 (by decide)]; exact B 4 rfl))
    fun b4 ⟨h4, e4⟩ => ?_
  have lk4 := lk3.trans (AltOp.lk h4 (by decide))
  have z4 : b4.gpr .x17 = 0 := (h4.gpr _ (by decide)).trans z3
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk4.scratch hs) 7 5 6 (by decide) (by decide) (by decide) z4)
    fun b5 ⟨h5, l5, e5⟩ => ?_
  have lk5 := lk4.trans (AltOp.lk h5 (by decide))
  have z5 : b5.gpr .x17 = 0 := (h5.gpr _ (by decide)).trans z4
  -- the bit, and the flag
  have c5 : b5.gpr .x19 = BitVec.ofNat 64 (i+1) := by
    rw [h5.gpr _ (by decide), h4.gpr _ (by decide), h3.gpr _ (by decide), h2.gpr _ (by decide),
      h1.gpr _ (by decide), ka.gpr _ (by decide)]; exact hcnt
  have w5 : word b5.mem base 768 = BitVec.ofNat 64 st.swap := by
    rw [AltOp.w768 h5, AltOp.w768 h4, AltOp.w768 h3, AltOp.w768 h2, AltOp.w768 h1, ka.mem]; exact hw
  rw [WP.block_append_iff]
  refine WP.mono (bitFlags_ok (lk5.scratch hs) hi hsw (bit_le k i) c5 w5
    (by rw [lk5.bit hi]; exact hb)) fun f ⟨lkf, gf, ef, cf, zf, wf, of⟩ => ?_
  have lkF := lk5.trans lkf
  have zF : f.gpr .x17 = 0 := (gf _ (by decide) (by decide) (by decide) (by decide)).trans z5
  have ofe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, fe f.mem base (offset j) = fe b5.mem base (offset j) := fun j =>
    of.fe (Or.inl (by simp only [offset]; omega)) (by simp only [offset]; omega)
  -- the point to double
  rw [WP.block_append_iff]
  refine WP.mono (muxE (lkF.scratch hs) 8 6 2 (by decide) (by decide) (by decide))
    fun c6 ⟨h6, zf6, _, e6⟩ => ?_
  have lk6 := lkF.trans (AltOp.lk h6 (by decide))
  have z6 : c6.gpr .x17 = 0 := (h6.gpr _ (by decide)).trans zF
  rw [WP.block_append_iff]
  refine WP.mono (muxE (lk6.scratch hs) 1 4 5 (by decide) (by decide) (by decide))
    fun c7 ⟨h7, _, _, e7⟩ => ?_
  have lk7 := lk6.trans (AltOp.lk h7 (by decide))
  have z7 : c7.gpr .x17 = 0 := (h7.gpr _ (by decide)).trans z6
  -- the products and squares
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk7.scratch hs) 3 4 2 (by decide) (by decide) (by decide) z7)
    fun c8 ⟨h8, l8, e8⟩ => ?_
  have lk8 := lk7.trans (AltOp.lk h8 (by decide))
  have z8 : c8.gpr .x17 = 0 := (h8.gpr _ (by decide)).trans z7
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk8.scratch hs) 8 8 (by decide) (by decide) z8)
    fun c9 ⟨h9, l9, e9⟩ => ?_
  have lk9 := lk8.trans (AltOp.lk h9 (by decide))
  have z9 : c9.gpr .x17 = 0 := (h9.gpr _ (by decide)).trans z8
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk9.scratch hs) 4 7 3 (by decide) (by decide) (by decide) z9
    (by rw [fr h9 3 (by decide)]; exact l8)) fun c10 ⟨h10, e10⟩ => ?_
  have lk10 := lk9.trans (AltOp.lk h10 (by decide))
  have z10 : c10.gpr .x17 = 0 := (h10.gpr _ (by decide)).trans z9
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk10.scratch hs) 1 1 (by decide) (by decide) z10)
    fun c11 ⟨h11, l11, e11⟩ => ?_
  have lk11 := lk10.trans (AltOp.lk h11 (by decide))
  have z11 : c11.gpr .x17 = 0 := (h11.gpr _ (by decide)).trans z10
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk11.scratch hs) 3 7 3 (by decide) (by decide) (by decide) z11
    (by rw [fr h11 7 (by decide), fr h10 7 (by decide), fr h9 7 (by decide), fr h8 7 (by decide),
      fr h7 7 (by decide), fr h6 7 (by decide), ofe]; exact l5)
    (by rw [fr h11 3 (by decide), fr h10 3 (by decide), fr h9 3 (by decide)]; exact l8))
    fun c12 ⟨h12, e12⟩ => ?_
  have lk12 := lk11.trans (AltOp.lk h12 (by decide))
  have z12 : c12.gpr .x17 = 0 := (h12.gpr _ (by decide)).trans z11
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk12.scratch hs) 4 4 (by decide) (by decide) z12)
    fun c13 ⟨h13, l13, e13⟩ => ?_
  have lk13 := lk12.trans (AltOp.lk h13 (by decide))
  have z13 : c13.gpr .x17 = 0 := (h13.gpr _ (by decide)).trans z12
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk13.scratch hs) 7 1 8 (by decide) (by decide) (by decide) z13
    (by rw [fr h13 8 (by decide), fr h12 8 (by decide), fr h11 8 (by decide),
      fr h10 8 (by decide)]; exact l9)) fun c14 ⟨h14, e14⟩ => ?_
  have lk14 := lk13.trans (AltOp.lk h14 (by decide))
  have z14 : c14.gpr .x17 = 0 := (h14.gpr _ (by decide)).trans z13
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk14.scratch hs) 3 3 (by decide) (by decide) z14)
    fun c15 ⟨h15, l15, e15⟩ => ?_
  have lk15 := lk14.trans (AltOp.lk h15 (by decide))
  have z15 : c15.gpr .x17 = 0 := (h15.gpr _ (by decide)).trans z14
  rw [WP.block_append_iff]
  refine WP.mono (cmaddA24_ok (lk15.scratch hs) z15)
    fun c16 ⟨lk16', z16, x16, _, o16, e16⟩ => ?_
  have lk16 := lk15.trans lk16'
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk16.scratch hs) 1 1 8 (by decide) (by decide) (by decide) z16)
    fun c17 ⟨h17, l17, e17⟩ => ?_
  have lk17 := lk16.trans (AltOp.lk h17 (by decide))
  have z17 : c17.gpr .x17 = 0 := (h17.gpr _ (by decide)).trans z16
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk17.scratch hs) 4 4 0 (by decide) (by decide) (by decide) z17)
    fun c18 ⟨h18, l18, e18⟩ => ?_
  have lk18 := lk17.trans (AltOp.lk h18 (by decide))
  have z18 : c18.gpr .x17 = 0 := (h18.gpr _ (by decide)).trans z17
  refine WP.mono (mulE (lk18.scratch hs) 2 7 2 (by decide) (by decide) (by decide) z18)
    fun t ⟨h19, l19, e19⟩ => ?_
  have lk19 := lk18.trans (AltOp.lk h19 (by decide))
  have o16fe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, j ≠ 2 → fe c16.mem base (offset j) = fe c15.mem base (offset j) :=
    fun j hj => o16.fe (apart j 2 hj) (by simp only [offset]; omega)
  refine ⟨lk19, ?_, ?_, ?_, ?_⟩
  · have henv : env t.mem base = altEnv (env s.mem base) (st.swap == bit k i) := by
      have g1 : env b1.mem base = gDm (env a.mem base) := e1
      have g2 : env b2.mem base = gSn (env b1.mem base) := e2
      have g3 : env b3.mem base = gDn (env b2.mem base) := e3
      have g4 : env b4.mem base = gSm (env b3.mem base) := e4
      have g5 : env b5.mem base = gDmsn (env b4.mem base) := e5
      have g6 : env c6.mem base = gD f.zf (env f.mem base) := e6
      have g7 : env c7.mem base = gS c6.zf (env c6.mem base) := e7
      have g8 : env c8.mem base = gDnsm (env c7.mem base) := e8
      have g9 : env c9.mem base = gD2 (env c8.mem base) := e9
      have g10 : env c10.mem base = gDpro (env c9.mem base) := e10
      have g11 : env c11.mem base = gS2 (env c10.mem base) := e11
      have g12 : env c12.mem base = gSpro (env c11.mem base) := e12
      have g13 : env c13.mem base = gDpro2 (env c12.mem base) := e13
      have g14 : env c14.mem base = gP (env c13.mem base) := e14
      have g15 : env c15.mem base = gXm (env c14.mem base) := e15
      have g16 : env c16.mem base = gE (env c15.mem base) := e16
      have g17 : env c17.mem base = gXn (env c16.mem base) := e17
      have g18 : env c18.mem base = gZm (env c17.mem base) := e18
      have g19 : env t.mem base = gZn (env c18.mem base) := e19
      rw [g19, g18, g17, g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, ef, g5, g4, g3, g2,
        g1, ka.mem, zf6, zf]
      rfl
    rw [henv]
    exact altEnv_ok _ k x1 st i hg hsw
  · rw [h19.gpr _ (by decide), h18.gpr _ (by decide), h17.gpr _ (by decide), x16,
      h15.gpr _ (by decide), h14.gpr _ (by decide), h13.gpr _ (by decide), h12.gpr _ (by decide),
      h11.gpr _ (by decide), h10.gpr _ (by decide), h9.gpr _ (by decide), h8.gpr _ (by decide),
      h7.gpr _ (by decide), h6.gpr _ (by decide)]
    exact cf
  · rw [AltOp.w768 h19, AltOp.w768 h18, AltOp.w768 h17, o16.word (Or.inr (by decide)) (by decide), AltOp.w768 h15,
      AltOp.w768 h14, AltOp.w768 h13, AltOp.w768 h12, AltOp.w768 h11, AltOp.w768 h10, AltOp.w768 h9, AltOp.w768 h8, AltOp.w768 h7, AltOp.w768 h6]
    exact wf
  · intro j hj
    rcases S14_cases j hj with rfl | rfl | rfl | rfl
    · rw [fr h19 1 (by decide), fr h18 1 (by decide)]; exact l17
    · exact l19
    · rw [fr h19 3 (by decide), fr h18 3 (by decide), fr h17 3 (by decide), o16fe 3 (by decide)]
      exact l15
    · rw [fr h19 4 (by decide)]; exact l18

/-- `x16 = x19 - 3`. -/
theorem cnt_ok (s : State) :
    WP isa (.block [.subImm .x .x16 .x19 3]) s fun t =>
      t.gpr .x16 = s.gpr .x19 - 3 ∧ Keeps [.x16] s t := by
  refine WP.block_cons_iff.mpr ⟨_, exec_subImm_x (d := .x16) (n := .x19) (imm := 3) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  simp only [State.read, BitVec.setWidth_eq]
  rfl

theorem step_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} {st : Ladder} {i : Nat}
    (hs : Scratch s base) (hi : i < 255) (hi3 : 3 ≤ i) (hg : Good (env s.mem base) x1 st)
    (hsw : st.swap ≤ 1) (hcnt : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hw : word s.mem base 768 = BitVec.ofNat 64 st.swap)
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i))
    (hB : Bel s.mem base S14) :
    WP isa (.block VG.Impl.X25519.AArch64.AltLadder.step) s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderStep k x1 st i) ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x16 = BitVec.ofNat 64 (i - 3) ∧
      word t.mem base 768 = BitVec.ofNat 64 (bit k i) ∧ Bel t.mem base S14 := by
  rw [VG.Impl.X25519.AArch64.AltLadder.step, WP.block_append_iff]
  refine WP.mono (body_ok hs hi hg hsw hcnt hw hb hB) fun u ⟨ku, gu, cu, wu, bu⟩ => ?_
  refine WP.mono (cnt_ok u) fun t ⟨t16, kt⟩ => ?_
  refine ⟨ku.trans (LoopKeep.of_keeps kt (by decide)), by rw [kt.mem]; exact gu,
    by rw [kt.gpr _ (by decide)]; exact cu, ?_, by rw [kt.mem]; exact wu,
    fun j hj => by rw [kt.mem]; exact bu j hj⟩
  rw [t16, cu]
  exact VG.Offset.ofNat_sub_ofNat hi3

end VG.Proof.X25519.AArch64.AltLadder
