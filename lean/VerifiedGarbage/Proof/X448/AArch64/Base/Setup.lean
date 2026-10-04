import VerifiedGarbage.Proof.X448.AArch64.Base.Combine
import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave
import VerifiedGarbage.Proof.X448.AArch64.Bits

/-!
# X448 of the base point on AArch64: the setup

Untrusted: everything here is checked by Lean. The setup points `x3` at the
working space, sets `x12`, saves the callee-saved registers and the output
pointer, zeroes every slot, expands the clamped scalar's bits, and starts both
accumulators at `[G] B` (`baseG`): `StepInv` for step 0.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 store_ok)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- A constant slot: its limbs from immediates, through `x4`. -/
theorem constSlot_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) (v : Spec.X448.Fe) :
    WP isa (.block (constSlot o v)) s fun t =>
      (∀ w < 8, word t.mem base (o + 8 * w) = limb v w) ∧ Outside base o 64 s.mem t.mem ∧
      Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (∀ w < n, word t.mem base (o + 8 * w) = limb v w) ∧ Outside base o 64 s.mem t.mem ∧ Keeps [.x4] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (const64 .x4 (limb v n) ++ [st .x4 (o + 8 * n)])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (VG.AArch64.Tbl.const64_ok t .x4 (limb v n)) fun a ⟨a4, ka, ea⟩ => ?_
    have kt : Keeps [.x4] t a := ⟨fun r hr => ka r (by simpa using hr), by rw [ea], by rw [ea]⟩
    have ha : Scr a base := (hs.of_keeps tk (by decide)).of_keeps kt (by decide)
    have am : a.mem = t.mem := by rw [ea]
    refine WP.mono (store_ok ha (by omega) (by omega) .x4) fun u ⟨um, uk⟩ => ⟨fun w hw => ?_, ?_, ?_⟩
    · rw [um, VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega)]
      by_cases h : w = n
      · subst h; rw [ite_eq_left rfl, a4]
      · rw [ite_eq_right (by omega), am]; exact tv w (by omega)
    · intro x hx
      rw [um, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega), am]
      exact tm x hx
    · exact (tk.trans kt).trans (uk.mono (by simp))
  have := wp_range_flatMap (M := isa) (N := 8) inv step 8 (le_refl _) s
    ⟨fun _ hw => absurd hw (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩
  exact this

open VG.Proof.X448.AArch64 (Saved)

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

theorem word_store {m : Mem} {base : Addr} {d e : Nat} (hd : d + 8 ≤ 8192) (he : e + 8 ≤ 8192)
    (hdm : d % 8 = 0) (hem : e % 8 = 0) (v : BitVec 64) (hne : e ≠ d) :
    word (m.writeW (off base d) v) base e = word m base e := by
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ hd he hdm hem, ite_eq_right hne]

theorem word_store_self {m : Mem} {base : Addr} {d : Nat} (hd : d + 8 ≤ 8192) (hdm : d % 8 = 0)
    (v : BitVec 64) : word (m.writeW (off base d) v) base d = v := by
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ hd hd hdm hdm, ite_eq_left rfl]

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

/-- The registers, the stores of `x19` and `x20`, the output pointer to `x20`, and the save of
`x21`–`x28`. -/
theorem prefix_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) ++ VG.Impl.X448.AArch64.Fast.save)) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      Keeps [.x3, .x12, .x20] s t ∧ Outside base 0 8192 s.mem t.mem := by
  rw [show ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
      st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) =
      [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ [.addImm .x .x20 .x0 0])) from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (regs_ok s) fun a ⟨a3, a12, ka, ma⟩ => ?_
  have ha : Scr a base := ⟨a3.trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  have b0 : word b.mem base 0 = s.gpr .x19 := by
    rw [mb, word_store_self (by decide) (by decide), ka.1 _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  have c0 : word c.mem base 0 = s.gpr .x19 := by
    rw [mc, word_store (by decide) (by decide) (by decide) (by decide) _ (by decide), b0]
  have c8 : word c.mem base 8 = s.gpr .x20 := by
    rw [mc, word_store_self (by decide) (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (mov20_ok c) fun d ⟨d20, md, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  refine WP.mono (save_ok hsd) fun t ⟨tx, tOut, tg, tr, tw⟩ => ?_
  have kad : Keeps [.x3, .x12, .x20] s d :=
    (((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans (kd.mono (by simp))
  have kt : Keeps [.x3, .x12, .x20] s t := ⟨fun r hr => (congrFun tg r).trans (kad.1 r hr), tr.trans kad.2.1,
    tw.trans kad.2.2⟩
  have od : Outside base 0 8192 s.mem d.mem := by
    have o1 : Outside base 0 8192 s.mem b.mem := by
      rw [mb, ← ma]; exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
    have o2 : Outside base 0 8192 b.mem c.mem := by
      rw [mc]; exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
    rw [md]; exact o1.trans o2
  refine ⟨hsd.of_keeps (rs := []) ⟨fun r _ => congrFun tg r, tr, tw⟩ (by decide), ⟨?_, ?_⟩, ?_, ?_, kt,
    od.trans (tOut.mono (by omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega))⟩
  · rw [tOut.word (Or.inl (by decide)) (by decide), md]; exact c0
  · rw [tOut.word (Or.inl (by decide)) (by decide), md]; exact c8
  · rw [congrFun tg .x20, d20, kc.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]
  · intro k hk
    rw [tx k hk]
    have : VG.Impl.X448.AArch64.Fast.saved k ∉ [Reg.x3, .x12, .x20] := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact kad.1 _ this

/-- The setup's first block: `prefix`, then `v8`–`v15` saved and every slot zeroed. -/
theorem block1_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) ++ VG.Impl.X448.AArch64.Fast.save ++
        VG.Impl.X448.AArch64.Fast.vsave ++ ([.movz .x .x4 0 0] : List Instr) ++
        (List.range 352).map (fun i => st .x4 (slot 0 + 8 * i)))) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      SavedV base s.v t.mem ∧ Keeps [.x3, .x12, .x4, .x20] s t ∧
      (∀ i < 352, limbs t.mem base (slot 0) i = 0) ∧ Outside base 0 8192 s.mem t.mem := by
  simp only [List.append_assoc]
  rw [← List.append_assoc (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr)), WP.block_append_iff]
  refine WP.mono (WP.preservedV (prefix_ok hb hw hn) (by lit_decide)) fun a ⟨⟨ha, sa, oa, xa, ka, outa⟩, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vsave_ok ha) fun b ⟨vb, ob, gb, rb, wb⟩ => ?_
  have hsb : Scr b base := ha.of_keeps (rs := []) ⟨fun r _ => congrFun gb r, rb, wb⟩ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroX4_ok b) fun c ⟨c4, mc, kc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.fill_ok hsc (o := slot 0) (n := 352) (by decide) (by decide) c4)
    fun t ⟨tz, tOut, kt⟩ => ?_
  have hst : Scr t base := hsc.of_keeps kt (by decide)
  have m : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 2880 ≤ d → d + 8 ≤ 8192 →
      d + 8 ≤ VG.Impl.X448.AArch64.Fast.VSAVE ∨ VG.Impl.X448.AArch64.Fast.VSAVE + 128 ≤ d →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by simp only [slot]; omega) h2, mc, ob.word h3 h2]
  have hxs : ∀ k < 8, word t.mem base (Impl.X448.AArch64.Fast.SAVE + 8 * k) = s.gpr (Impl.X448.AArch64.Fast.saved k) :=
    fun k hk => by
      rw [m (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, Impl.X448.AArch64.Fast.VSAVE]; omega)]
      exact xa k hk
  have vt : SavedV base a.v t.mem := by
    have vc : SavedV base a.v c.mem := by rw [mc]; exact vb
    exact vc.outside tOut (by simp only [slot, Impl.X448.AArch64.Fast.VSAVE]; omega)
  refine ⟨hst, ⟨by rw [m (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [m (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kc.1 _ (by decide), congrFun gb .x20]; exact oa,
    hxs, fun k hk => ?_, ?_, tz, ?_⟩
  · rw [vt k hk]
    have hr : VG.Impl.Curve448.AArch64.Neon.V (8 + k) ∈ preservedV := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact va _ hr
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kt.1 _ (by simp), kc.1 _ (by simpa using hr.2.2.1), congrFun gb r,
        ka.1 _ (by simp [hr.1, hr.2.1, hr.2.2.2])]
    · rw [kt.2.1, kc.2.1, rb, ka.2.1]
    · rw [kt.2.2, kc.2.2, wb, ka.2.2]
  · refine (outa.trans (ob.mono (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega)
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega))).trans ?_
    rw [← mc]; exact tOut.mono (by simp only [slot]; omega) (by simp only [slot]; omega)

/-- The constant slots: both accumulators at `[G] B`, and the counter at 0. -/
theorem consts_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (constSlot AX Impl.X448.baseG.1 ++ constSlot AY Impl.X448.baseG.2 ++ constSlot AZ 1 ++
        constSlot BX Impl.X448.baseG.1 ++ constSlot BY Impl.X448.baseG.2 ++ constSlot BZ 1 ++
        ([.movz .x .x19 0 0] : List Instr))) s fun t =>
      (∀ w < 8, word t.mem base (AX + 8 * w) = limb Impl.X448.baseG.1 w ∧
        word t.mem base (AY + 8 * w) = limb Impl.X448.baseG.2 w ∧ word t.mem base (AZ + 8 * w) = limb 1 w ∧
        word t.mem base (BX + 8 * w) = limb Impl.X448.baseG.1 w ∧
        word t.mem base (BY + 8 * w) = limb Impl.X448.baseG.2 w ∧ word t.mem base (BZ + 8 * w) = limb 1 w) ∧
      Outside base 64 768 s.mem t.mem ∧ Keeps [.x4, .x19] s t ∧ t.gpr .x19 = 0 := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok hs (o := AX) (by decide) (by decide) _) fun t1 ⟨v1, o1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h1 (o := AY) (by decide) (by decide) _) fun t2 ⟨v2, o2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h2 (o := AZ) (by decide) (by decide) _) fun t3 ⟨v3, o3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h3 (o := BX) (by decide) (by decide) _) fun t4 ⟨v4, o4, k4⟩ => ?_
  have h4 := h3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h4 (o := BY) (by decide) (by decide) _) fun t5 ⟨v5, o5, k5⟩ => ?_
  have h5 := h4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h5 (o := BZ) (by decide) (by decide) _) fun t6 ⟨v6, o6, k6⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok t6 0 (by decide))
    fun t ⟨c, g, m, rd, wr⟩ => ⟨fun w hw => ?_, ?_, ?_, by rw [c]; rfl⟩
  · have hw8 : w < 8 := hw
    simp only [AX, AY, AZ, BX, BY, BZ, slot] at v1 v2 v3 v4 v5 v6 o1 o2 o3 o4 o5 o6 ⊢
    rw [m]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega), o4.word (by omega) (by omega),
        o3.word (by omega) (by omega), o2.word (by omega) (by omega)]; exact v1 w hw8
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega), o4.word (by omega) (by omega),
        o3.word (by omega) (by omega)]; exact v2 w hw8
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega), o4.word (by omega) (by omega)]
      exact v3 w hw8
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega)]; exact v4 w hw8
    · rw [o6.word (by omega) (by omega)]; exact v5 w hw8
    · exact v6 w hw8
  · simp only [AX, AY, AZ, BX, BY, BZ, slot] at o1 o2 o3 o4 o5 o6
    rw [m]
    exact (((((o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))).trans
      (o3.mono (by omega) (by omega))).trans (o4.mono (by omega) (by omega))).trans
      (o5.mono (by omega) (by omega))).trans (o6.mono (by omega) (by omega))
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r hr.2, k6.1 r (by simp [hr.1]), k5.1 r (by simp [hr.1]), k4.1 r (by simp [hr.1]),
        k3.1 r (by simp [hr.1]), k2.1 r (by simp [hr.1]), k1.1 r (by simp [hr.1])]
    · rw [rd, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    · rw [wr, k6.2.2, k5.2.2, k4.2.2, k3.2.2, k2.2.2, k1.2.2]

theorem F_of_words {m : Mem} {base : Addr} {o : Nat} {v : Spec.X448.Fe}
    (h : ∀ w < 8, word m base (o + 8 * w) = limb v w) : VG.Proof.X448.AArch64.Weak.F m base o = v := by
  simp only [VG.Proof.X448.AArch64.Weak.F]
  rw [VG.Proof.X448.Wide.valN_congr (fun w hw => show (word m base (o + 8 * w)).toNat = _ by rw [h w hw]),
    limb_val, VG.Proof.X448.toFe_self]

theorem bnd_of_words {m : Mem} {base : Addr} {o : Nat} {v : Spec.X448.Fe}
    (h : ∀ w < 8, word m base (o + 8 * w) = limb v w) : Bnd Ib m base o := fun w hw => by
  show (word m base (o + 8 * w)).toNat < _
  rw [h w hw]; exact Nat.lt_of_lt_of_le (limb_lt v w) (by decide)

open VG.Proof.Ed448 (Rep baseAff)
open VG.Proof.X448.AArch64 (bitRegs ofs)

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

/-- What the setup leaves, from the function's entry state `sE`. -/
structure Ready (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  inv : StepInv t base k 0 t
  saved : Saved base sE.gpr t.mem
  out : t.gpr .x20 = sE.gpr .x0
  savedX : SavedX base sE.gpr t.mem
  savedV : SavedV base sE.v t.mem
  lr : t.gpr .x30 = sE.gpr .x30
  rd : t.rd = sE.rd
  wr : t.wr = sE.wr
  mem : Outside base 0 8192 sE.mem t.mem

theorem setup_ok {s : State} {base kp : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (hk : s.gpr .x1 = kp)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.AArch64.ofs base (kp + BitVec.ofNat 64 q)) :
    WP isa VG.Impl.X448.AArch64.Base.setup s
      (Ready s base (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem kp 56))) := by
  unfold VG.Impl.X448.AArch64.Base.setup
  refine WP.seq (WP.mono (block1_ok hb hw hn) fun a ⟨ha, sa, oa, xa, va, ka, za, outa⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun b ⟨gb, rdb, wrb, ob, bitsb⟩ => ?_)
  have kb : Keeps bitRegs a b := ⟨gb, rdb, wrb⟩
  have hsb : Scr b base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  refine WP.mono (consts_ok hsb) fun t ⟨tv, tOut, kt, tc⟩ => ?_
  have hst : Scr t base := hsb.of_keeps kt (by decide)
  -- Every word outside the constant slots and the bits is as `block1` left it.
  have wt : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 832 ≤ d → d + 8 ≤ BITS ∨ BITS + 448 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by omega) h3, ob.word h2 h3]
  -- The slots `block1` zeroed.
  have zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := za (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  have zt : ∀ i : Index, 6 ≤ i.val → ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i hi w hw => by
    have := i.isLt
    rw [wt (by simp only [slot]; omega) (by simp only [slot, BITS]; omega) (by simp only [slot]; omega)]
    exact zs i w hw
  have ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
      VG.Proof.X448.AArch64.Weak.E t.mem base i = v := fun i v h => F_of_words h
  have pA : pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 0 1 2 = VG.Proof.X448.basePt Impl.X448.baseG := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
  have pB : pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 3 4 5 = VG.Proof.X448.basePt Impl.X448.baseG := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
      ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
  have hG : Rep (VG.Proof.X448.basePt Impl.X448.baseG) (((VG.Proof.X448.baseGVal : ℤ) + 0) • baseAff) := by
    rw [add_zero, natCast_zsmul]; exact VG.Proof.X448.baseG_ok
  have bsaved : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 832 ≤ d → d + 8 ≤ BITS ∨ BITS + 448 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := wt
  refine ⟨⟨by decide, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
      by rw [pA]; exact hG, by rw [pB]; exact hG, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩,
    ⟨by rw [bsaved (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [bsaved (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [bsaved (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)]
      exact xa k hk,
    (va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega)).outside tOut
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kt.2.1, kb.2.1, ka.2.1], by rw [kt.2.2, kb.2.2, ka.2.2],
    (outa.trans (ob.mono (by omega) (by simp only [BITS]; omega))).trans (tOut.mono (by omega) (by omega))⟩
  · -- Every slot's limbs are below `Ib`.
    by_cases hi : i.val < 6
    · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega
      rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact bnd_of_words (fun w hw => (tv w hw).1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
    · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
      rw [zt i (by omega) w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 (by decide) w hw]; rfl
  · have hn' := hn
    rw [tOut _ (by rw [Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact bitsb q hq

end VG.Proof.X448.AArch64.Base
