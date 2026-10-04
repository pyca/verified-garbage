import VerifiedGarbage.Proof.Ed448.AArch64.BaseField
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main

/-!
# Ed448 base-point multiplication on AArch64: the entry and the constants

`entry`: `x3` the working space, `x12 = 2^28 - 1`, `x19` and `x20` saved in
its first 16 bytes, the output pointer in `x20`, and every slot zeroed.
`baseConsts`: `R` the neutral point (slot 0 is already zero), `B` in slots
8–10 and `d` in slot 11, each from immediates (`constSlot`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Saved store_ok
  word_write_aligned writeW_outside zeroX4_ok fill_ok)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Proof.X448.AArch64.Base (constSlot_ok F_of_words limb_lt)
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Impl.X448.AArch64.Base (constSlot limb)

/-- `x3 := x2` (the working space) and `x12 := 2²⁸ - 1`. -/
theorem regs_ok (s : State) :
    WP isa (.block ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x3 = s.gpr .x2 ∧ t.gpr .x12 = 0x0fffffff ∧ Keeps [.x3, .x12] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by decide, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mov20_ok (s : State) :
    WP isa (.block [.addImm .x .x20 .x0 0]) s fun t =>
      t.gpr .x20 = s.gpr .x0 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The registers, the saves of `x19` and `x20`, and `x4 = 0`. -/
theorem head_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0, .movz .x .x4 0 0] : List Instr)) s fun t =>
      Scr t base ∧ t.gpr .x20 = s.gpr .x0 ∧ t.gpr .x4 = 0 ∧ Saved base s.gpr t.mem ∧
      Outside base 0 16 s.mem t.mem ∧ Keeps [.x3, .x12, .x20, .x4] s t := by
  rw [show ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
      st .x19 0, st .x20 8, .addImm .x .x20 .x0 0, .movz .x .x4 0 0] : List Instr) =
      [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ ([.addImm .x .x20 .x0 0] ++ [.movz .x .x4 0 0]))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (regs_ok s) fun a ⟨a3, a12, ka, ma⟩ => ?_
  have ha : Scr a base := ⟨a3.trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mov20_ok c) fun d ⟨d20, md, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  refine WP.mono (zeroX4_ok d) fun t ⟨t4, mt, kt⟩ => ?_
  have k : Keeps [.x3, .x12, .x20, .x4] s t :=
    ((((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans
      (kd.mono (by simp))).trans (kt.mono (by simp))
  have ob : Outside base 0 16 s.mem b.mem := by
    rw [mb, ← ma]; exact (writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
  have oc : Outside base 0 16 b.mem c.mem := by
    rw [mc]; exact (writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
  refine ⟨hsd.of_keeps kt (by decide), by rw [kt.1 _ (by decide), d20, kc.1 _ (by decide),
      kb.1 _ (by decide), ka.1 _ (by decide)], t4, ⟨?_, ?_⟩, by rw [mt, md]; exact ob.trans oc, k⟩
  · rw [mt, md, mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), mb, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, ka.1 _ (by decide)]
  · rw [mt, md, mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, kb.1 _ (by decide), ka.1 _ (by decide)]

/-- A constant slot: its value, every slot's words below `2^56`, and the
other slots unchanged. -/
theorem constStep_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i : Fin 22, ∀ w < 8, (word s.mem base (slot i.val + 8 * w)).toNat < 2 ^ 56)
    (o : Fin 22) (v : Spec.X448.Fe) :
    WP isa (.block (constSlot (slot o.val) v)) s fun t =>
      (∀ i : Fin 22, ∀ w < 8, (word t.mem base (slot i.val + 8 * w)).toNat < 2 ^ 56) ∧
      E t.mem base o = v ∧ (∀ i : Fin 22, i ≠ o → E t.mem base i = E s.mem base i) ∧
      Outside base (slot o.val) 64 s.mem t.mem ∧ Keeps [.x4] s t := by
  have ho := o.isLt
  refine WP.mono (constSlot_ok hs (o := slot o.val) (by simp only [slot]; omega) (by simp only [slot]; omega) v)
    fun t ⟨tv, tm, tk⟩ => ⟨fun i w hw => ?_, F_of_words tv, fun i hi => ?_, tm, tk⟩
  · by_cases h : i = o
    · subst h; rw [tv w hw]; exact limb_lt v w
    · have hsep := VG.Proof.X448.AArch64.Weak.slot_sep h
      rw [tm.word (by omega) (by have := i.isLt; simp only [slot]; omega)]
      exact hb i w hw
  · have hsep := VG.Proof.X448.AArch64.Weak.slot_sep hi
    exact VG.Proof.X448.AArch64.Weak.E_outside tm i (by omega)

theorem limb_zero (w : Nat) : limb 0 w = 0 := by
  rw [limb, Fin.val_zero, Nat.zero_shiftRight, Nat.zero_mod]; rfl

/-- The constants, from zeroed slots: every slot's limbs below `2^56`, `R`
the neutral point, `B` the base point and `d`. -/
theorem baseConsts_ok {s : State} {base : Addr} (hs : Scr s base)
    (hz : ∀ i : Fin 22, ∀ w < 8, word s.mem base (slot i.val + 8 * w) = 0) :
    WP isa (.block baseConsts) s fun t =>
      BoundedEnv t.mem base ∧ pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧
      pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧ E t.mem base 11 = Spec.Ed448.d ∧
      Outside base 64 2816 s.mem t.mem ∧ Keeps [.x4] s t := by
  have b0 : ∀ i : Fin 22, ∀ w < 8, (word s.mem base (slot i.val + 8 * w)).toNat < 2 ^ 56 :=
    fun i w hw => by rw [hz i w hw]; decide
  have e0 : E s.mem base 0 = 0 := F_of_words fun w hw => by rw [limb_zero]; exact hz 0 w hw
  simp only [baseConsts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constStep_ok hs b0 1 1) fun t1 ⟨b1, v1, o1, m1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constStep_ok h1 b1 2 1) fun t2 ⟨b2, v2, o2, m2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constStep_ok h2 b2 8 _) fun t3 ⟨b3, v3, o3, m3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constStep_ok h3 b3 9 _) fun t4 ⟨b4, v4, o4, m4, k4⟩ => ?_
  have h4 := h3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constStep_ok h4 b4 10 1) fun t5 ⟨b5, v5, o5, m5, k5⟩ => ?_
  have h5 := h4.of_keeps k5 (by decide)
  refine WP.mono (constStep_ok h5 b5 11 _) fun t ⟨b6, v6, o6, m6, k6⟩ => ?_
  refine ⟨fun i w hw => Nat.lt_trans (b6 i w hw) (by decide), ?_, ?_, v6, ?_,
    (((((k1.trans k2).trans k3).trans k4).trans k5).trans k6)⟩
  · simp only [pt, Spec.Ed448.identity]
    rw [o6 0 (by decide), o5 0 (by decide), o4 0 (by decide), o3 0 (by decide), o2 0 (by decide),
      o1 0 (by decide), e0, o6 1 (by decide), o5 1 (by decide), o4 1 (by decide), o3 1 (by decide),
      o2 1 (by decide), v1, o6 2 (by decide), o5 2 (by decide), o4 2 (by decide), o3 2 (by decide), v2]
  · simp only [pt]
    rw [o6 8 (by decide), o5 8 (by decide), o4 8 (by decide), v3, o6 9 (by decide), o5 9 (by decide), v4,
      o6 10 (by decide), v5]
    rfl
  · simp only [slot] at m1 m2 m3 m4 m5 m6
    exact (((((m1.mono (by omega) (by omega)).trans (m2.mono (by omega) (by omega))).trans
      (m3.mono (by omega) (by omega))).trans (m4.mono (by omega) (by omega))).trans
      (m5.mono (by omega) (by omega))).trans (m6.mono (by omega) (by omega))

/-- The entry and the constants. -/
theorem prep_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (entry ++ baseConsts)) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧
      Keeps [.x3, .x12, .x20, .x4] s t ∧ Outside base 0 8192 s.mem t.mem ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧
      pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧ E t.mem base 11 = Spec.Ed448.d := by
  rw [entry, List.append_assoc, WP.block_append_iff]
  refine WP.mono (head_ok hb hw hn) fun a ⟨ha, a20, a4, sa, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok ha (o := slot 0) (n := 352) (by decide) (by decide) a4) fun b ⟨zb, ob, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  have zs : ∀ i : Fin 22, ∀ w < 8, word b.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := zb (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show limbs b.mem base (slot 0) (16 * i.val + w) = (word b.mem base (slot i.val + 8 * w)).toNat by
      simp only [limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  refine WP.mono (baseConsts_ok hsb zs) fun t ⟨bt, pR, pB, dt, ot, kt⟩ => ?_
  refine ⟨hsb.of_keeps kt (by decide), bt, (sa.outside ob (by decide)).outside ot (by decide),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact a20,
    (ka.trans (kb.mono (by simp))).trans (kt.mono (by simp)), ?_, pR, pB, dt⟩
  exact ((oa.mono (by omega) (by omega)).trans (ob.mono (by simp only [slot]; omega)
    (by simp only [slot]; omega))).trans (ot.mono (by omega) (by omega))

end VG.Proof.Ed448.AArch64
