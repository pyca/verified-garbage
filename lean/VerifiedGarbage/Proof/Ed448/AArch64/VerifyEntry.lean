import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Proof.X448.AArch64.Weak.Ops
import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448 verification's equation on AArch64: the entry and the constants

`ventry`: `x12 = 2^28 - 1`, `x19` and `x20` saved in the working space's
first 16 bytes, `x20 = 0` (no check has failed), every slot zeroed, then `B`
in slots 8–10 and `d` in slot 11, each from immediates (`constSlot`). A
constant slot keeps every slot's limbs bounded (`constE_ok`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Saved store_ok
  word_write_aligned writeW_outside fill_ok)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv E_outside slot_sep)
open VG.Proof.X448.AArch64.Base (constSlot_ok F_of_words limb_lt)
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Impl.X448.AArch64.Base (constSlot limb)

theorem limb_zero (w : Nat) : limb 0 w = 0 := by
  rw [limb, Fin.val_zero, Nat.zero_shiftRight, Nat.zero_mod]; rfl

/-- `x12 := 2²⁸ - 1`. -/
theorem mask12_ok (s : State) :
    WP isa (.block ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x12 = 0x0fffffff ∧ Keeps [.x12] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem zero20_ok (s : State) :
    WP isa (.block [.movz .x .x20 0 0]) s fun t =>
      t.gpr .x20 = 0 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- The mask, the saves of `x19` and `x20`, `x20 = 0` and `x4 = 0`. -/
theorem vhead_ok {s : State} {base : Addr} (hb : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1, st .x19 0, st .x20 8,
        .movz .x .x20 0 0, .movz .x .x4 0 0] : List Instr)) s fun t =>
      Scr t base ∧ t.gpr .x20 = 0 ∧ t.gpr .x4 = 0 ∧ Saved base s.gpr t.mem ∧
      Outside base 0 16 s.mem t.mem ∧ Keeps [.x12, .x20, .x4] s t := by
  rw [show ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1, st .x19 0, st .x20 8,
      .movz .x .x20 0 0, .movz .x .x4 0 0] : List Instr) =
      [.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ ([.movz .x .x20 0 0] ++ [.movz .x .x4 0 0]))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (mask12_ok s) fun a ⟨a12, ka, ma⟩ => ?_
  have ha : Scr a base := ⟨(ka.1 _ (by decide)).trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero20_ok c) fun d ⟨d20, md, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.zeroX4_ok d) fun t ⟨t4, mt, kt⟩ => ?_
  have k : Keeps [.x12, .x20, .x4] s t :=
    ((((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans
      (kd.mono (by simp))).trans (kt.mono (by simp))
  have ob : Outside base 0 16 s.mem b.mem := by
    rw [mb, ← ma]; exact (writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
  have oc : Outside base 0 16 b.mem c.mem := by
    rw [mc]; exact (writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
  refine ⟨hsd.of_keeps kt (by decide), by rw [kt.1 _ (by decide)]; exact d20, t4, ⟨?_, ?_⟩,
    by rw [mt, md]; exact ob.trans oc, k⟩
  · rw [mt, md, mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), mb, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, ka.1 _ (by decide)]
  · rw [mt, md, mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, kb.1 _ (by decide), ka.1 _ (by decide)]

/-- A constant slot, among bounded ones: its value, every slot still bounded,
and the other slots unchanged. -/
theorem constE_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (o : Fin 22) (v : Spec.X448.Fe) :
    WP isa (.block (constSlot (slot o.val) v)) s fun t =>
      BoundedEnv t.mem base ∧ E t.mem base o = v ∧ (∀ i : Fin 22, i ≠ o → E t.mem base i = E s.mem base i) ∧
      Outside base (slot o.val) 64 s.mem t.mem ∧ Keeps [.x4] s t := by
  have ho := o.isLt
  refine WP.mono (constSlot_ok hs (o := slot o.val) (by simp only [slot]; omega) (by simp only [slot]; omega) v)
    fun t ⟨tv, tm, tk⟩ => ⟨fun i j hj => ?_, F_of_words tv, fun i hi => ?_, tm, tk⟩
  · by_cases h : i = o
    · subst h
      show (word t.mem base (slot i.val + 8 * j)).toNat < _
      rw [tv j hj]
      exact Nat.lt_of_lt_of_le (limb_lt v j) (by decide)
    · have hsep := slot_sep h
      rw [show limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j from
        tm.limbs (by omega) (by have := i.isLt; simp only [slot]; omega) (by omega)]
      exact hb i j hj
  · have hsep := slot_sep hi
    exact E_outside tm i (by omega)

/-- The constants, from zeroed slots: every slot bounded, slot 0 zero, `B`
and `d`. -/
theorem vconsts_ok {s : State} {base : Addr} (hs : Scr s base)
    (hz : ∀ i : Fin 22, ∀ w < 8, word s.mem base (slot i.val + 8 * w) = 0) :
    WP isa (.block (constSlot (slot 8) Spec.Ed448.basePoint.X ++ (constSlot (slot 9) Spec.Ed448.basePoint.Y ++
      (constSlot (slot 10) 1 ++ constSlot (slot 11) Spec.Ed448.d)))) s fun t =>
      BoundedEnv t.mem base ∧ E t.mem base 0 = 0 ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Outside base 64 2816 s.mem t.mem ∧ Keeps [.x4] s t := by
  have b0 : BoundedEnv s.mem base := fun i w hw => by
    show (word s.mem base (slot i.val + 8 * w)).toNat < _
    rw [hz i w hw]; decide
  have e0 : E s.mem base 0 = 0 := F_of_words fun w hw => by rw [limb_zero]; exact hz 0 w hw
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok hs b0 8 _) fun t1 ⟨b1, v1, o1, m1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok h1 b1 9 _) fun t2 ⟨b2, v2, o2, m2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok h2 b2 10 1) fun t3 ⟨b3, v3, o3, m3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  refine WP.mono (constE_ok h3 b3 11 _) fun t ⟨b4, v4, o4, m4, k4⟩ => ?_
  refine ⟨b4, ?_, ?_, v4, ?_, ((k1.trans k2).trans k3).trans k4⟩
  · rw [o4 0 (by decide), o3 0 (by decide), o2 0 (by decide), o1 0 (by decide), e0]
  · simp only [pt]
    rw [o4 8 (by decide), o3 8 (by decide), o2 8 (by decide), v1, o4 9 (by decide), o3 9 (by decide), v2,
      o4 10 (by decide), v3]
    rfl
  · simp only [slot] at m1 m2 m3 m4
    exact (((m1.mono (by omega) (by omega)).trans (m2.mono (by omega) (by omega))).trans
      (m3.mono (by omega) (by omega))).trans (m4.mono (by omega) (by omega))

/-- The entry: the registers, the saves, the zeroed slots and the constants. -/
theorem ventry_ok {s : State} {base : Addr} (hb : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = 0 ∧
      Keeps [.x12, .x20, .x4] s t ∧ Outside base 0 8192 s.mem t.mem ∧
      E t.mem base 0 = 0 ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d := by
  rw [ventry]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (vhead_ok hb hw hn) fun a ⟨ha, a20, a4, sa, oa, ka⟩ => ?_
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
  refine WP.mono (vconsts_ok hsb zs) fun t ⟨bt, e0, pB, dt, ot, kt⟩ => ?_
  refine ⟨hsb.of_keeps kt (by decide), bt, (sa.outside ob (by decide)).outside ot (by decide),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact a20,
    (ka.trans (kb.mono (by simp))).trans (kt.mono (by simp)), ?_, e0, pB, dt⟩
  exact ((oa.mono (by omega) (by omega)).trans (ob.mono (by simp only [slot]; omega)
    (by simp only [slot]; omega))).trans (ot.mono (by omega) (by omega))

end VG.Proof.Ed448.AArch64
