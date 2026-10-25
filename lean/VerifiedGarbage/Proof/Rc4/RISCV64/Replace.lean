module

public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-! # RC4 on RISC-V: replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-! ## Moving the difference to the byte's lane -/

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 8)
    (h4 : s.gpr .a4 = idx.setWidth 64) (h6 : s.gpr .t6 = 0#64) (hax : s.gpr .a5 = c.setWidth 64)
    (h1 : s.gpr .t1 = spread c (idx.toNat % 8) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .t1 = spread c (idx.toNat % 8) j ∧ t.gpr .a5 = s.gpr .a5 ∧
      t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t6 = s.gpr .t6 ∧ t.mem = s.mem := by
  unfold spreadStep laneMask isZero
  rrun [h4, h6, hax, h1, show j < 2048 by omega]
  rw [lane_mask idx hj, and_allOnes_ite, spread_succ]

theorem spread_steps (s₀ : State) (idx c : Byte) (h4 : s₀.gpr .a4 = idx.setWidth 64)
    (h6 : s₀.gpr .t6 = 0#64) (hax : s₀.gpr .a5 = c.setWidth 64) :
    ∀ n ≤ 8, ∀ s, s.gpr .t1 = spread c (idx.toNat % 8) n → s.gpr .a5 = s₀.gpr .a5 →
      s.gpr .a4 = s₀.gpr .a4 → s.gpr .t6 = s₀.gpr .t6 → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .t1 = spread c (idx.toNat % 8) 0 ∧ t.gpr .a5 = s₀.gpr .a5 ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h1 hax' _ _ hm; exact WP.block_nil ⟨h1, hax', hm⟩
  | succ n ih =>
    intro s h1 hax' h4' h6' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (spread_step s idx c (by omega) (h4'.trans h4) (h6'.trans h6)
      (hax'.trans hax) h1) fun t ⟨t1, tax, t4, t6, tm⟩ => ?_
    exact ih (by omega) t t1 (tax.trans hax') (t4.trans h4') (t6.trans h6') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 8).reverse := rfl

/-! ## Storing back every doubleword -/

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h4 : s.gpr .a4 = idx.setWidth 64) (h6 : s.gpr .t6 = 0#64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .a7 + BitVec.ofNat 64 (8 * k))
        (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 64 ^^^
          (if idx.toNat / 8 = k then s.gpr .t1 else 0#64)) ∧
      t.gpr .t1 = s.gpr .t1 ∧ t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a7 = s.gpr .a7 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hal' := al_add hal (d := 8 * k) (by omega) (by omega)
  unfold scatterStep rowMask isZero
  rrun [h4, h6, hr, hw, hal', show 8 * k < 2048 by omega]
  rw [row_mask idx hk, allOnes_and_ite]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h4 : s₀.gpr .a4 = idx.setWidth 64) (h6 : s₀.gpr .t6 = 0#64) (hal : (s₀.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s₀.wr (s₀.gpr .a7) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .t1 = d → s.gpr .a4 = s₀.gpr .a4 → s.gpr .t6 = s₀.gpr .t6 →
      s.gpr .a7 = s₀.gpr .a7 → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (s₀.gpr .a7) idx.toNat d n ∧ t.gpr .t1 = d ∧
        t.gpr .a4 = s₀.gpr .a4 ∧ t.gpr .t6 = s₀.gpr .t6 ∧ t.gpr .a7 = s₀.gpr .a7 ∧
        t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h1 h4' h6' hp hwr hm
    refine WP.block_nil ⟨?_, h1, h4', h6', hp, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h1 h4' h6' hp hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h1 h4' h6' hp hwr hm) fun t ⟨tm, t1, t4, t6, tp, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .a7 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tp]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hw
    refine WP.mono (scatter_step t idx (by omega) (t4.trans h4) (t6.trans h6) (by rw [tp]; exact hal)
      hq) fun u ⟨um, u1, u4, u6, up, _, uwr⟩ => ?_
    refine ⟨?_, u1.trans t1, u4.trans t4, u6.trans t6, up.trans tp, uwr.trans twr⟩
    rw [um, tm, t1, tp, scatter_succ]

/-! ## The replacement -/

theorem replace_core (s : State) (idx ii : Byte) (h4 : s.gpr .a4 = idx.setWidth 64)
    (h6 : s.gpr .t6 = 0#64) (hcx : s.gpr .a3 = ii.setWidth 64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .a5 = (s.mem (s.gpr .a7 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 :=
    region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .a7 + ii.setWidth 64) 1 := by
    rw [byte_addr]; exact hi
  let p := s.gpr .a7
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2] (lookup_core s idx h4 h6 hal hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have t4 : t.gpr .a4 = s.gpr .a4 := tk.gpr (by decide)
  have t6 : t.gpr .t6 = s.gpr .t6 := tk.gpr (by decide)
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have tcx : t.gpr .a3 = s.gpr .a3 := tk.gpr (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  have h1 : WP isa (.block (loadI ++ ([.logic .xor .a5 .a5 .t0, .li .t1 0] : List Instr))) t
      fun u =>
      u.gpr .a5 = (b ^^^ v).setWidth 64 ∧ u.gpr .t1 = 0#64 ∧ u.gpr .a4 = s.gpr .a4 ∧
        u.gpr .t6 = s.gpr .t6 ∧ u.gpr .a7 = s.gpr .a7 ∧ u.gpr .a3 = s.gpr .a3 ∧ u.mem = s.mem ∧
        u.rd = s.rd ∧ u.wr = s.wr := by
    unfold loadI
    rrun [hit, tax, tm, t4, t6, tp, tcx, tk.2.1, tk.2.2, hcx]
    rw [byte_addr ii, xor_byte]
  refine WP.mono h1 fun u ⟨uax, u1, u4, u6, up, ucx, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) (u4.trans h4) (u6.trans h6) uax 8 (by decide) u
    (by rw [u1]; unfold spread; rw [ite_eq_right (by omega)]) rfl rfl rfl rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.t0, .t1, .t2] hsp (by decide +kernel))
    fun w ⟨⟨w1, wax, wm⟩, wk⟩ => ?_
  have w4 : w.gpr .a4 = s.gpr .a4 := (wk.gpr (by decide)).trans u4
  have w6 : w.gpr .t6 = s.gpr .t6 := (wk.gpr (by decide)).trans u6
  have wp : w.gpr .a7 = s.gpr .a7 := (wk.gpr (by decide)).trans up
  have wcx : w.gpr .a3 = s.gpr .a3 := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  rw [← List.append_assoc, WP.block_append_iff]
  have h2 : WP isa (.block (loadI ++ ([.logic .xor .a5 .a5 .t0] : List Instr))) w
      fun x => x.gpr .a5 = b.setWidth 64 ∧ x.gpr .t1 = w.gpr .t1 ∧ x.gpr .a4 = s.gpr .a4 ∧
        x.gpr .t6 = s.gpr .t6 ∧ x.gpr .a7 = s.gpr .a7 ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    unfold loadI
    rrun [hit, wax, uax, wm, um, w4, w6, wp, wcx, wwr, wrd, hcx]
    rw [byte_addr ii, xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x1, x4, x6, xp, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.t0, .t2]
    (scatter_steps s idx _ h4 h6 hal hw 32 (by decide) x rfl x4 x6 xp xwr xm)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x1, w1]
  unfold scatter spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.RISCV64
