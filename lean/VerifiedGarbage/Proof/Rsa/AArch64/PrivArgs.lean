import VerifiedGarbage.Proof.Rsa.AArch64.PrivFrame

/-!
# `vg_rsa_private_checked` on AArch64: the arguments of the CRT

`saveSlots` keeps our arguments in the slots (`saveSlots_ok`), `copyArgs`
copies our last ten stack arguments to the bottom of the inner frame as the
CRT's (`copyArgs_ok`, one word at a time), and `crtRegs` sets its arguments
in registers (`crtRegs_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The registers a block writes, other than the callee-saved ones. -/
macro "priv_cs_tac" : tactic => `(tactic| (
  intro r hr _
  revert hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]))

/-- Six words stored in the slots. -/
theorem six_ok (B : Addr) (_hB : B.toNat + 128 ≤ 2 ^ 64) (m : Mem) (a b c d e f : BitVec 64) :
    let m' := (((((m.writeW (B + BitVec.ofNat 64 80) a).writeW (B + BitVec.ofNat 64 88) b).writeW
      (B + BitVec.ofNat 64 96) c).writeW (B + BitVec.ofNat 64 104) d).writeW (B + BitVec.ofNat 64 112) e).writeW
      (B + BitVec.ofNat 64 120) f
    Frame [⟨B + BitVec.ofNat 64 80, 48⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 80) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 88) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 96) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 104) 64 = d ∧ m'.readW (B + BitVec.ofNat 64 112) 64 = e ∧
      m'.readW (B + BitVec.ofNat 64 120) 64 = f := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 128 → y + 8 ≤ 128 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 80 ≤ x → x + 8 ≤ 128 →
      (⟨B + BitVec.ofNat 64 80, 48⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 80 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 88 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 96 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 104 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 112 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 120 (by omega) (by omega)), ?_, ?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 80 120 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 80 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 80 104 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 80 96 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 80 88 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 88 120 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 88 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 88 104 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 88 96 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 96 120 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 96 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 96 104 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 104 120 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 104 112 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 112 120 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- Our arguments in registers. -/
structure Regs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.inp

theorem saveSlots_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hr : Regs L t) :
    WP isa (.block saveSlots) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Regs L t' ∧
      t'.gpr .x15 = L.B ∧ Frame [⟨L.B + BitVec.ofNat 64 80, 48⟩] t.mem t'.mem := by
  have hnB := hL.nB
  have w := fun d (h : d + 8 ≤ frameBytes) => hc.inFrW hL (d := d) (n := 8) h
  have w80 := w 80 (by decide)
  have w88 := w 88 (by decide)
  have w96 := w 96 (by decide)
  have w104 := w 104 (by decide)
  have w112 := w 112 (by decide)
  have w120 := w 120 (by decide)
  apply WP.of_runBlock
  simp only [saveSlots, oOut, oN, oK, oE, oEl, oIn, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false,
    ite_true, hc.sp, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w80, w88, w96,
    w104, w112, w120, write8, Option.some.injEq, exists_eq_left', BitVec.add_zero]
  obtain ⟨f, k80, k88, k96, k104, k112, k120⟩ := six_ok L.B (by omega) t.mem (t.gpr .x0) (t.gpr .x2)
    (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6)
  refine ⟨hc.store hL rfl rfl (hc.sp.symm ▸ rfl) rfl
    (by priv_cs_tac) (Frame.sub f fun r hr => ?_), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, f⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.FR, by simp, Offset.sub_base _ (by decide)⟩
  all_goals try simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
  exacts [k80.trans hr.x0, k88.trans hr.x2, k96.trans hr.x3, k104.trans hr.x4, k112.trans hr.x5,
    k120.trans hr.x6, hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6]

/-- After copying `j` of the CRT's stack arguments, from `t₀`. -/
structure CopyInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t₀ : State) (j : Nat)
    (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  slots : Slots L t.mem
  regs : Regs L t
  x15 : t.gpr .x15 = L.B
  frame : Frame [⟨L.B, 80⟩] t₀.mem t.mem
  args : ∀ i < j, t.mem.readW (L.B + BitVec.ofNat 64 (8 * i)) 64 = m₀.readW (L.B + BitVec.ofNat 64 (arg (i + 2))) 64

theorem copyArg_ok (hL : L.Ok) {t₀ t : State} {j : Nat} (hj : j < 10) (hI : CopyInv L g vv m₀ t₀ j t) :
    WP isa (.block (copyArg j)) t (CopyInv L g vv m₀ t₀ (j + 1)) := by
  have hnB := hL.nB
  have hc := hI.ctx
  have la := hc.inArgs hL (j := j + 2) (by omega)
  have aw := hc.argW hL (j := j + 2) (by omega)
  have w := hc.inFrW hL (d := 8 * j) (n := 8) (by simp only [frameBytes]; omega)
  apply WP.of_runBlock
  simp only [copyArg, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, hI.x15, la, w, read8, aw, write8, Option.some.injEq, exists_eq_left',
    show 8 * j % 8 = 0 by omega, show 8 * j < 4096 * 8 by omega, show arg (j + 2) % 8 = 0 by
      simp only [arg, frameBytes]; omega, show arg (j + 2) < 32768 by simp only [arg, frameBytes]; omega,
    and_self]
  have hfr : Frame [L.FR] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (8 * j))
      (m₀.readW (L.B + BitVec.ofNat 64 (arg (j + 2))) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by simp only [frameBytes]; omega) (by omega))
  have hf80 : Frame [⟨L.B, 80⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (8 * j))
      (m₀.readW (L.B + BitVec.ofNat 64 (arg (j + 2))) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) hfr, hI.slots.frame hf80 (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have := Offset.disjoint_base L.B (d := oOut) (n := 48) (k := 80) (by decide) (by simp only [oOut]; omega)
      exact this) (by omega), ?_, ?_, hI.frame.trans hf80, fun i hi => ?_⟩
  · have r := hI.regs
    exact ⟨r.x0, r.x2, r.x3, r.x4, r.x5, r.x6⟩
  · exact hI.x15
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hI.args i hi
    · exact Mem.readW_writeW_self64 _ _ _

theorem copyArgs_upto (hL : L.Ok) {t₀ : State} :
    ∀ n ≤ 10, ∀ t, CopyInv L g vv m₀ t₀ 0 t →
      WP isa (.block ((List.range n).flatMap copyArg)) t (CopyInv L g vv m₀ t₀ n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, t, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyArgs_upto hL n (by omega) t h) fun t' h' => copyArg_ok hL (by omega) h'

/-- The arguments of the CRT in registers, and on the stack at `B`. -/
structure CrtArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.B + BitVec.ofNat 64 oM
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.inp
  x5 : t.gpr .x5 = L.k
  x6 : t.gpr .x6 = L.p
  x7 : t.gpr .x7 = L.pl
  stk : ∀ i < 10, t.mem.readW (L.B + BitVec.ofNat 64 (8 * i)) 64 = L.argv (i + 2)

theorem crtRegs_ok (hL : L.Ok) {t₀ t : State} (ha : ArgsAt L m₀) (hI : CopyInv L g vv m₀ t₀ 10 t) :
    WP isa (.block crtRegs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ CrtArgs L t' ∧
      Frame [⟨L.B, 80⟩] t₀.mem t'.mem := by
  have hc := hI.ctx
  have l0 := hc.inArgs hL (j := 0) (by omega)
  have l1 := hc.inArgs hL (j := 1) (by omega)
  have a0 := (hc.argW hL (j := 0) (by omega)).trans (ha 0 (by omega))
  have a1 := (hc.argW hL (j := 1) (by omega)).trans (ha 1 (by omega))
  apply WP.of_runBlock
  simp only [crtRegs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, l0, l1, read8, a0, a1,
    Option.some.injEq, exists_eq_left', show arg 0 % 8 = 0 by decide, show arg 0 < 32768 by decide,
    show arg 1 % 8 = 0 by decide, show arg 1 < 32768 by decide, show oM < 4096 by decide, and_self,
    show (0 : Nat) < 4096 by decide]
  have r := hI.regs
  refine ⟨hc.regs rfl rfl rfl rfl rfl (by priv_cs_tac), hI.slots, ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    fun i hi => (hI.args i hi).trans (ha _ (by omega))⟩, hI.frame⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq,
    BitVec.add_zero, r.x2, r.x3, r.x6]

end

end VG.Proof.Rsa.AArch64
