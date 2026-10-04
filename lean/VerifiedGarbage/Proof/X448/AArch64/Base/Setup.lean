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

/-- The registers, the stores of `x19`, `x20` and the output pointer, and the save of `x21`–`x28`. -/
theorem prefix_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, st .x0 OUT] : List Instr) ++ VG.Impl.X448.AArch64.Fast.save)) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ word t.mem base OUT = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      Keeps [.x3, .x12] s t := by
  rw [show ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
      st .x19 0, st .x20 8, st .x0 OUT] : List Instr) =
      [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ [st .x0 OUT])) from rfl]
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
  refine WP.mono (store_ok hsc (d := OUT) (by decide) (by decide) .x0) fun d ⟨md, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  have d0 : word d.mem base 0 = s.gpr .x19 := by
    rw [md, word_store (by decide) (by decide) (by decide) (by decide) _ (by decide), c0]
  have d8 : word d.mem base 8 = s.gpr .x20 := by
    rw [md, word_store (by decide) (by decide) (by decide) (by decide) _ (by decide), c8]
  have dO : word d.mem base OUT = s.gpr .x0 := by
    rw [md, word_store_self (by decide) (by decide), kc.1 _ (by decide), kb.1 _ (by decide),
      ka.1 _ (by decide)]
  refine WP.mono (save_ok hsd) fun t ⟨tx, tOut, tg, tr, tw⟩ => ?_
  have kad : Keeps [.x3, .x12] s d := ((ka.trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans
    (kd.mono (by simp))
  have kt : Keeps [.x3, .x12] s t := ⟨fun r hr => (congrFun tg r).trans (kad.1 r hr), tr.trans kad.2.1,
    tw.trans kad.2.2⟩
  refine ⟨hsd.of_keeps (rs := []) ⟨fun r _ => congrFun tg r, tr, tw⟩ (by decide), ⟨?_, ?_⟩, ?_, ?_, kt⟩
  · rw [tOut.word (Or.inl (by decide)) (by decide)]; exact d0
  · rw [tOut.word (Or.inl (by decide)) (by decide)]; exact d8
  · rw [tOut.word (Or.inl (by decide)) (by decide)]; exact dO
  · intro k hk
    rw [tx k hk]
    have : VG.Impl.X448.AArch64.Fast.saved k ∉ [Reg.x3, .x12] := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact kad.1 _ this

/-- The setup's first block: `prefix`, then `v8`–`v15` saved and every slot zeroed. -/
theorem block1_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, st .x0 OUT] : List Instr) ++ VG.Impl.X448.AArch64.Fast.save ++
        VG.Impl.X448.AArch64.Fast.vsave ++ ([.movz .x .x4 0 0] : List Instr) ++
        (List.range 352).map (fun i => st .x4 (slot 0 + 8 * i)))) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ word t.mem base OUT = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      SavedV base s.v t.mem ∧ Keeps [.x3, .x12, .x4] s t ∧
      (∀ i < 352, limbs t.mem base (slot 0) i = 0) := by
  simp only [List.append_assoc]
  rw [← List.append_assoc (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, st .x0 OUT] : List Instr)), WP.block_append_iff]
  refine WP.mono (WP.preservedV (prefix_ok hb hw hn)) fun a ⟨⟨ha, sa, oa, xa, ka⟩, va⟩ => ?_
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
    by rw [m (by decide) (by decide) (by decide)]; exact oa,
    hxs, fun k hk => ?_, ?_, tz⟩
  · rw [vt k hk]
    have hr : VG.Impl.Curve448.AArch64.Neon.V (8 + k) ∈ preservedV := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact va _ hr
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kt.1 _ (by simp), kc.1 _ (by simpa using hr.2.2), congrFun gb r, ka.1 _ (by simp [hr.1, hr.2.1])]
    · rw [kt.2.1, kc.2.1, rb, ka.2.1]
    · rw [kt.2.2, kc.2.2, wb, ka.2.2]

end VG.Proof.X448.AArch64.Base
