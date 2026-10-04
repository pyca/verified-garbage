import VerifiedGarbage.Proof.Ed448.AArch64.BaseField
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters

/-!
# Ed448 base-point multiplication on AArch64: one bit

`step`: the counter `x19` counts down to the bit `t`; `R` (slots 0–2) is
doubled, `T = R + B` computed into slots 3–5, and `T` swapped into `R` with
the mask of byte `t` of `BITS` (the bit). Only the slots, the products'
coefficients, the counter and the registers `workRegs` change.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off contains_sc read1_eq Outside2 workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap decCounter_ok)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (BITS ACC slot)

theorem mask_bit : ∀ b < 2, (0 : BitVec 64) - (BitVec.ofNat 8 b).setWidth 64 = mask (decide (b = 1)) := by
  decide

/-- `x6` := the mask of the bit at `BITS + x19`. -/
theorem bitMask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hc : s.gpr .x19 = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block ([.add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS, .movz .x .x6 0 0,
        .sub .x .x6 .x6 .x4] : List Instr)) s fun s' =>
      s'.gpr .x6 = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.x4, .x6, .x11] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have enc : BITS % 1 = 0 ∧ BITS < 4096 * 1 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, hc, hs.x3, addr, enc, and_self,
    Offset.add_add, Nat.add_comm t BITS, State.load,
    hin, read1_eq, hbit, Option.bind_some, Option.map_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have ext : (BitVec.setWidth 32 (BitVec.ofNat 8 b)).setWidth 64 = (BitVec.ofNat 8 b).setWidth 64 := by
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  simp only [ext, e0]
  refine ⟨mask_bit b hb2, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

/-- The slots after an iteration, for the bit `sw`. -/
def stepEnv (sw : Bool) (e : Fin 22 → Spec.X448.Fe) : Fin 22 → Spec.X448.Fe :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (evalOps addOps (evalOps doubleOps e))))

theorem stepEnv_pt (sw : Bool) (e : Fin 22 → Spec.X448.Fe) :
    pt (stepEnv sw e) 0 1 2 =
      if sw then addWith (e 11) (double (pt e 0 1 2)) (pt e 8 9 10) else double (pt e 0 1 2) := by
  cases sw <;> rfl

theorem stepEnv_q (sw : Bool) (e : Fin 22 → Spec.X448.Fe) : pt (stepEnv sw e) 8 9 10 = pt e 8 9 10 := by
  cases sw <;> rfl

theorem stepEnv_d (sw : Bool) (e : Fin 22 → Spec.X448.Fe) : stepEnv sw e 11 = e 11 := by
  cases sw <;> rfl

/-- The swaps of `T` into `R`. -/
theorem swaps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot 0) (slot 3) ++
        (Impl.Curve448.AArch64.cswap (slot 1) (slot 4) ++ Impl.Curve448.AArch64.cswap (slot 2) (slot 5)))) s
      fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
        E t.mem base = opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (E s.mem base))) := by
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs hb 0 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (tk.scr hs) tb 1 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, uc, ue⟩ => ?_
  refine WP.mono (cswapE (uk.scr (tk.scr hs)) ub 2 5 (by decide) (uc.trans (tc.trans hm)))
    fun v ⟨vk, vb, _, ve⟩ => ⟨(tk.trans uk).trans vk, vb, by rw [ve, ue, te]⟩

/-- An iteration, for the bit `t` (`b`). -/
theorem step_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {t : Nat}
    (ht : t < 456) (hc : s.gpr .x19 = BitVec.ofNat 64 (t + 1)) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa step s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 t ∧ (s'.gpr .x19 == 0) = decide (t = 0) ∧
      Keeps (.x19 :: workRegs) s s' ∧ BoundedEnv s'.mem base ∧
      Outside2 base 64 2816 ACC 512 s.mem s'.mem ∧
      E s'.mem base = stepEnv (decide (b = 1)) (E s.mem base) := by
  rw [step, WP.seq_iff]
  refine WP.mono (decCounter_ok (by omega) hc) fun s1 ⟨c1, g1, m1, rd1, wr1, z1⟩ => ?_
  have hs1 : Scr s1 base :=
    ⟨(g1 _ (by decide)).trans hs.x3, (g1 _ (by decide)).trans hs.mask, wr1 ▸ hs.wr, hs.nowrap⟩
  have hb1 : BoundedEnv s1.mem base := m1 ▸ hbd
  rw [WP.seq_iff]
  refine WP.mono (field_ok doubleOps doubleOps_valid hs1 hb1) fun s2 ⟨k2, b2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.seq_iff]
  refine WP.mono (field_ok addOps addOps_valid hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have k13 := k2.trans k3
  have c3 : s3.gpr .x19 = BitVec.ofNat 64 t := (k13.regs.1 _ (by decide)).trans c1
  have hbit3 : s3.mem (off base (BITS + t)) = BitVec.ofNat 8 b := by
    have hofs : VG.Proof.X448.AArch64.ofs base (off base (BITS + t)) = BITS + t :=
      Mem.sub_ofNat_toNat base (by simp only [BITS]; omega)
    rw [k13.mem _ (by rw [hofs]; simp only [BITS]; omega) (by rw [hofs]; simp only [BITS, ACC]; omega), m1]
    exact hbit
  rw [select]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (bitMask_ok hs3 ht c3 hb2 hbit3) fun s4 ⟨x4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base :=
    ⟨(g4 _ (by decide)).trans hs3.x3, (g4 _ (by decide)).trans hs3.mask, wr4 ▸ hs3.wr, hs3.nowrap⟩
  have b4 : BoundedEnv s4.mem base := m4 ▸ b3
  refine WP.mono (swaps_ok hs4 b4 x4) fun s' ⟨k', b', e'⟩ => ?_
  have g' : s'.gpr .x19 = BitVec.ofNat 64 t := by
    rw [k'.regs.1 _ (by decide), g4 _ (by decide)]; exact c3
  refine ⟨g', by rw [g', ← c1]; exact z1, ?_, b', ?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hw : r ∉ workRegs := fun h => hr (List.mem_cons_of_mem _ h)
      rw [k'.regs.1 r hw, g4 r (fun h => hw (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> decide)), k13.regs.1 r hw,
        g1 r (fun h => hr (h ▸ List.mem_cons_self))]
    · rw [k'.regs.2.1, rd4, k13.regs.2.1, rd1]
    · rw [k'.regs.2.2, wr4, k13.regs.2.2, wr1]
  · rw [← m1]
    exact k13.mem.trans ((by rw [m4]; exact Outside2.refl _ _ _ _ _ _ : Outside2 base 64 2816 ACC 512 s3.mem s4.mem).trans k'.mem)
  · rw [e', m4, e3, e2, m1]
    rfl

end VG.Proof.Ed448.AArch64
