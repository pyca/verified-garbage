module

import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.Range

/-! ### `Rc4.RISCV64.Frame`, which this module and modules that import it used -/

section

/-! # RC4 on RISC-V: the table in the frame

The table is kept in a frame on the stack, copied there from the context
(`table_copy`), and the frame is zeroed before returning (`wipe_ok`). -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4

/-- A table copied byte for byte. -/
theorem table_copy {m m' : Mem} {p q : Addr}
    (h : ∀ k < 256, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    (contextAt m' q).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  exact h k hk

/-- The context, from its table and its two indices. -/
theorem context_of {m : Mem} {p : Addr} {c : Context} (ht : (contextAt m p).table = c.table)
    (hi : m (p + 256#64) = c.i) (hj : m (p + 257#64) = c.j) : contextAt m p = c :=
  context_ext ht hi hj

/-- The doublewords of the frame zeroed. -/
theorem wipe_ok (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7) 256) :
    WP isa (.block wipe) s fun t => Frame [⟨s.gpr .a7, 256⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hw' : wipe = (List.range 32).flatMap fun k => [.store .d .t6 .a7 (8 * k)] := by
    rfl
  rw [hw']
  refine wp_range_flatMap (M := isa) (fun _ t => Frame [⟨s.gpr .a7, 256⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) (fun k t hk h => ?_) 32
    (Nat.le_refl _) s ⟨Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  obtain ⟨hf, hg, hrd, hwr, hsp⟩ := h
  refine Wp.wp_sd (a := s.gpr .a7 + BitVec.ofNat 64 (8 * k)) (by omega_using [hk]) (by rw [hg])
    (al_add hal (by omega_using []) (by omega_using [hk]))
    (by rw [hwr]; exact region_offset _ _ _ _ _ (by omega_using [hk]) (by omega_using [hk]) hw) fun u hu =>
    WP.block_nil ⟨?_, hu.gpr.trans hg, hu.rd.trans hrd, hu.wr.trans hwr, hu.sp.trans hsp⟩
  rw [hu.mem]
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))

end VG.Proof.Rc4.RISCV64

end

end

/-! ### `Rc4.RISCV64.Replace`, which this module and modules that import it used -/

section

/-! # RC4 on RISC-V: replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-! ## Storing back every doubleword -/

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h5 : s.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8)) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .a7 + BitVec.ofNat 64 (8 * k))
        (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 64 ^^^
          (if idx.toNat / 8 = k then s.gpr .t1 else 0#64)) ∧
      t.gpr .t1 = s.gpr .t1 ∧ t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t5 = s.gpr .t5 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a7 = s.gpr .a7 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hal' := al_add hal (d := 8 * k) (by omega_using []) (by omega_using [hk])
  unfold scatterStep rowMask
  rrun [h5, hr, hw, hal', show 8 * k < 2048 by omega_using [hk], show 63 - k < 64 by omega_using []]
  rw [row_bit idx hk, allOnes_and_ite]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h5 : s₀.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8)) (hal : (s₀.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s₀.wr (s₀.gpr .a7) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .t1 = d → s.gpr .a4 = s₀.gpr .a4 → s.gpr .t5 = s₀.gpr .t5 →
      s.gpr .t6 = s₀.gpr .t6 → s.gpr .a7 = s₀.gpr .a7 → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (s₀.gpr .a7) idx.toNat d n ∧ t.gpr .t1 = d ∧
        t.gpr .a4 = s₀.gpr .a4 ∧ t.gpr .t5 = s₀.gpr .t5 ∧ t.gpr .t6 = s₀.gpr .t6 ∧
        t.gpr .a7 = s₀.gpr .a7 ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h1 h4' h5' h6' hp hwr hm
    refine WP.block_nil ⟨?_, h1, h4', h5', h6', hp, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h1 h4' h5' h6' hp hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s h1 h4' h5' h6' hp hwr hm) fun t ⟨tm, t1, t4, t5, t6, tp, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .a7 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tp]
      exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) hw
    refine WP.mono (scatter_step t idx (by omega_using [hn]) (t5.trans h5) (by rw [tp]; exact hal)
      hq) fun u ⟨um, u1, u4, u5, u6, up, _, uwr⟩ => ?_
    refine ⟨?_, u1.trans t1, u4.trans t4, u5.trans t5, u6.trans t6, up.trans tp, uwr.trans twr⟩
    rw [um, tm, t1, tp, scatter_succ]

/-! ## The replacement -/

theorem replace_core (s : State) (idx ii : Byte) (h4 : s.gpr .a4 = idx.setWidth 64)
    (hcx : s.gpr .a3 = ii.setWidth 64) (hal : (s.gpr .a7).toNat % 8 = 0)
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
    region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hr
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .a7 + ii.setWidth 64) 1 := by
    rw [byte_addr]; exact hi
  let p := s.gpr .a7
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5] (lookup_core s idx h4 hal hr) (by decide +kernel))
    fun t ⟨⟨tax, t5, tm⟩, tk⟩ => ?_
  have t4 : t.gpr .a4 = s.gpr .a4 := tk.gpr (by decide)
  have t6 : t.gpr .t6 = s.gpr .t6 := tk.gpr (by decide)
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have tcx : t.gpr .a3 = s.gpr .a3 := tk.gpr (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  have h1 : WP isa (.block (loadI ++ ([.logic .xor .a5 .a5 .t0] : List Instr))) t
      fun u =>
      u.gpr .a5 = (b ^^^ v).setWidth 64 ∧ u.gpr .a4 = s.gpr .a4 ∧ u.gpr .t5 = t.gpr .t5 ∧
        u.gpr .t6 = s.gpr .t6 ∧ u.gpr .a7 = s.gpr .a7 ∧ u.gpr .a3 = s.gpr .a3 ∧ u.mem = s.mem ∧
        u.rd = s.rd ∧ u.wr = s.wr := by
    unfold loadI
    rrun [hit, tax, tm, t4, t6, tp, tcx, tk.2.1, tk.2.2, hcx]
    rw [byte_addr ii, xor_byte]
  refine WP.mono h1 fun u ⟨uax, u4, u5, u6, up, ucx, um, urd, uwr⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  have hsp : WP isa (.block (laneShift ++ ([.shiftReg .sll .d .t1 .a5 .t2] : List Instr))) u fun w =>
      w.gpr .t1 = (b ^^^ v).setWidth 64 <<< (8 * (idx.toNat % 8)) ∧ w.mem = u.mem := by
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.t2] (laneShift_run u idx (u4.trans h4)) (by decide +kernel) rfl)
      fun w ⟨⟨w2, wm⟩, wk⟩ => ?_
    have wax : w.gpr .a5 = u.gpr .a5 := wk.gpr (by decide)
    rrun [w2, wax, uax, wm]
  refine WP.mono (WP.keep [.t1, .t2] hsp (by decide +kernel) rfl) fun w ⟨⟨w1, wm⟩, wk⟩ => ?_
  have wax : w.gpr .a5 = u.gpr .a5 := wk.gpr (by decide)
  have w4 : w.gpr .a4 = s.gpr .a4 := (wk.gpr (by decide)).trans u4
  have w5 : w.gpr .t5 = t.gpr .t5 := (wk.gpr (by decide)).trans u5
  have w6 : w.gpr .t6 = s.gpr .t6 := (wk.gpr (by decide)).trans u6
  have wp : w.gpr .a7 = s.gpr .a7 := (wk.gpr (by decide)).trans up
  have wcx : w.gpr .a3 = s.gpr .a3 := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  rw [← List.append_assoc, WP.block_append_iff]
  have h2 : WP isa (.block (loadI ++ ([.logic .xor .a5 .a5 .t0] : List Instr))) w
      fun x => x.gpr .a5 = b.setWidth 64 ∧ x.gpr .t1 = w.gpr .t1 ∧ x.gpr .a4 = s.gpr .a4 ∧
        x.gpr .t5 = t.gpr .t5 ∧ x.gpr .t6 = s.gpr .t6 ∧ x.gpr .a7 = s.gpr .a7 ∧ x.mem = s.mem ∧
        x.wr = s.wr := by
    unfold loadI
    rrun [hit, wax, uax, wm, um, w4, w5, w6, wp, wcx, wwr, wrd, hcx]
    rw [byte_addr ii, xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x1, x4, x5, x6, xp, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.t0, .t2]
    (scatter_steps x idx _ (x5.trans t5) (by rw [xp]; exact hal) (by rw [xwr, xp]; exact hw) 32 (by decide) x
      rfl rfl rfl rfl rfl rfl rfl)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x1, w1, xm, xp]
  unfold scatter
  rw [ite_eq_left (by omega_using []), writeW_byte, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.RISCV64

end

end

/-! ### `Rc4.RISCV64.ApplyLoop`, which only this module used -/

section

/-! ### `Rc4.RISCV64.ApplyStep`, which only this module used -/

section

/-! # RC4 on RISC-V: one PRGA step, on the table in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- `i += 1`, then `j += S[i]`, copied to the index of the replacement. -/
def applyBefore : List Instr :=
  ([.addi .a3 .a3 1, .shift .sll .d .a3 .a3 56, .shift .srl .d .a3 .a3 56] : List Instr) ++ loadI ++
    ([.add .t4 .t4 .t0, .shift .sll .d .t4 .t4 56, .shift .srl .d .t4 .t4 56, .logic .or .a4 .t4 .t4] :
      List Instr)

/-- `S[i] := S[j]` (in `a5`), and the index `S[i] + S[j]` of the keystream byte. -/
def applyMiddle : List Instr :=
  loadI ++ ([.store .b .a5 .t2 0, .add .a4 .a5 .t0, .shift .sll .d .a4 .a4 56,
    .shift .srl .d .a4 .a4 56] : List Instr)

/-- The keystream byte XORed into the data. -/
def applyAfter : List Instr :=
  [.load .b .t0 .a1 0, .logic .xor .t0 .t0 .a5, .store .b .t0 .a1 0, .addi .a1 .a1 1,
    .addi .a2 .a2 (-1)]

theorem applyStep_eq :
    applyStep = applyBefore ++ (replace ++ (applyMiddle ++ (lookup ++ applyAfter))) := by
  simp only [applyStep, applyBefore, applyMiddle, applyAfter, List.append_assoc]

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block applyBefore) s fun t =>
      t.gpr .a3 = (i + 1#8).setWidth 64 ∧
      t.gpr .t4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.t0, .a3, .t4, .a4, .t2] s t ∧ t.mem = s.mem := by
  obtain hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + (i + 1#8).setWidth 64) 1 := by
    rw [byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega_using [])
      (by have := (i + 1#8).isLt; omega_using []) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .a3 = (i + 1#8).setWidth 64 ∧
      t.gpr .t4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.t0, .a3, .t4, .a4, .t2] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  unfold applyBefore loadI
  rrun [hcx, h7, byte_inc, hi, BitVec.or_self]
  rw [byte_addr (i + 1#8), byte_add]

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .a3 = ii.setWidth 64) (hax : s.gpr .a5 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block applyMiddle) s fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .a4 = (b + s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.t0, .a4, .t2] s t := by
  obtain hw' : InRegions s.wr (s.gpr .a7 + ii.setWidth 64) 1 := by rw [byte_addr ii]; exact hw
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .a4 = (b + s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.t0, .a4, .t2] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold applyMiddle loadI
  rrun [hcx, hax, hw', hr, low_byte, byte_add]
  rw [byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .a5 = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .a1) 1) :
    WP isa (.block applyAfter) s fun t =>
      t.mem = s.mem.write (s.gpr .a1) 1 (s.mem (s.gpr .a1) ^^^ k) ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧
      Keep [.t0, .a1, .a2] s t := by
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a1) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a1) 1 (s.mem (s.gpr .a1) ^^^ k) ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64) [.t0, .a1, .a2] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  unfold applyAfter
  rrun [hax, hd, hr, low_xor]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .a7 + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .a7 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .a7 + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .a1) 1 (swapped (s.gpr .a1) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧
      t.gpr .a3 = ii.setWidth 64 ∧ t.gpr .t4 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [applyStep_eq, WP.block_append_iff]
  refine WP.mono (apply_before s i j hcx h7 hr) fun t ⟨tcx, t7, t9, tk, tm⟩ => ?_
  obtain tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  obtain t0' : t.gpr .a0 = s.gpr .a0 := tk.gpr (by decide)
  obtain t1 : t.gpr .a1 = s.gpr .a1 := tk.gpr (by decide)
  obtain t2 : t.gpr .a2 = s.gpr .a2 := tk.gpr (by decide)
  obtain t6 : t.gpr .t6 = s.gpr .t6 := tk.gpr (by decide)
  obtain htp : InRegions t.wr (t.gpr .a7) 256 := by rw [tk.2.2, tp]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5]
    (replace_core t jj ii t9 tcx (by rw [tp]; exact hal) htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tp] at uax um
  obtain ucx : u.gpr .a3 = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  obtain u7 : u.gpr .t4 = jj.setWidth 64 := (uk.gpr (by decide)).trans t7
  obtain up : u.gpr .a7 = s.gpr .a7 := (uk.gpr (by decide)).trans tp
  obtain u0 : u.gpr .a0 = s.gpr .a0 := (uk.gpr (by decide)).trans t0'
  obtain u1 : u.gpr .a1 = s.gpr .a1 := (uk.gpr (by decide)).trans t1
  obtain u2 : u.gpr .a2 = s.gpr .a2 := (uk.gpr (by decide)).trans t2
  obtain u6 : u.gpr .t6 = s.gpr .t6 := (uk.gpr (by decide)).trans t6
  obtain urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  obtain uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  obtain hw : InRegions u.wr (u.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, up]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hp
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  obtain ha : u.mem (u.gpr .a7 + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, up, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [up, um] at vm
  have hvm : v.mem = swapped := vm
  obtain v9' : v.gpr .a4 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  obtain vp : v.gpr .a7 = s.gpr .a7 := (vk.gpr (by decide)).trans up
  obtain v6 : v.gpr .t6 = s.gpr .t6 := (vk.gpr (by decide)).trans u6
  obtain vrd : v.rd = s.rd := vk.2.1.trans urd
  obtain vwr : v.wr = s.wr := vk.2.2.trans uwr
  obtain hvp : InRegions (v.rd ++ v.wr) (v.gpr .a7) 256 := by rw [vrd, vwr, vp]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5]
    (lookup_core v (a + b) v9' (by rw [vp]; exact hal) hvp)
    (by decide +kernel)) fun w ⟨⟨wax, _, wm⟩, wk⟩ => ?_
  rw [hvm, vp] at wax
  obtain w0 : w.gpr .a0 = s.gpr .a0 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u0)
  obtain w1 : w.gpr .a1 = s.gpr .a1 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u1)
  obtain w2 : w.gpr .a2 = s.gpr .a2 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u2)
  obtain wp : w.gpr .a7 = s.gpr .a7 := (wk.gpr (by decide)).trans vp
  obtain w6 : w.gpr .t6 = s.gpr .t6 := (wk.gpr (by decide)).trans v6
  obtain wrd : w.rd = s.rd := wk.2.1.trans vrd
  obtain wwr : w.wr = s.wr := wk.2.2.trans vwr
  obtain hwd : InRegions w.wr (w.gpr .a1) 1 := by rw [wwr, w1]; exact hd
  refine WP.mono (apply_after w k wax hwd) fun z ⟨zm, z1, z2, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wp,
    (zk.gpr (by decide)).trans w6, (zk.gpr (by decide)).trans w0, ?_, ?_, ?_, ?_⟩
  · rw [zm, wm, hvm, w1]
  · rw [z1, w1]
  · rw [z2, w2]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u7]

end VG.Proof.Rc4.RISCV64

end

end


/-! # RC4 on RISC-V: the stream loop, on the table in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1)
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .a7)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .a7)).table = next.1.table ∧
      t.gpr .a3 = next.1.i.setWidth 64 ∧ t.gpr .t4 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .a1) = s.mem (s.gpr .a1) ^^^ next.2 ∧
      StreamFrame (s.gpr .a7) (s.gpr .a1) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hcx h7 hal hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h6', ha0, h1, h2, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h6', ha0, h1, h2⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .a1 ≠ s.gpr .a7 + BitVec.ofNat 64 idx.toNat := by
      intro he
      obtain hn := hs (s.gpr .a1) (by rw [he, Mem.sub_ofNat_toNat _ (by omega_using [])]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    obtain ht := table_swap s.mem (s.gpr .a7) (i + 1#8)
      (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1)
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .a1 + 1#64) n = bytesAt s.mem (s.gpr .a1 + 1#64) n := by
  refine WP.mono (apply_step s i j hcx h7 hal hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega_using [hn])
    (sep_symm (Offset.sep_base (s.gpr .a1) (by decide) (by omega_using [hn])))]
  exact bytes_table_frame _ _ _ _ _ (by omega_using [hn]) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .a7)).table =
    (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.table
  i : t.gpr .a3 = (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.i.setWidth 64
  j : t.gpr .t4 = (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .a1) n = (update ctx (bytesAt s.mem (s.gpr .a1) n)).2
  frame : StreamFrame (s.gpr .a7) (s.gpr .a1) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .a7 = s.gpr .a7
  zero : t.gpr .t6 = s.gpr .t6
  ctx : t.gpr .a0 = s.gpr .a0

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .a7)).table = ctx.table)
    (hcx : s.gpr .a3 = ctx.i.setWidth 64) (h7 : s.gpr .t4 = ctx.j.setWidth 64)
    (h6 : s.gpr .t6 = 0#64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hlen : s.gpr .a2 = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .a7) 256)
    (hd : InRegions s.wr (s.gpr .a1) (n + 1))
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) (n + 1)) :
    WP isa (.loop (.block applyStep) (.nonzero .a2)) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .a1) 1 := hd
    obtain hctx : ({ table := (contextAt s.mem (s.gpr .a7)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    obtain hstep := apply_step_table s ctx.i ctx.j hcx h7 hal hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, h60, ha0, _, hcount⟩ := ht
    have hbytes (m : Mem) : bytesAt m (s.gpr .a1) 1 = [m (s.gpr .a1)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · rw [Steps.eval_nonzero, hcount, hlen]
      rfl
    · constructor
      · simpa only [Nat.zero_add, hbytes, update] using htab
      · simpa only [Nat.zero_add, hbytes, update] using hti
      · simpa only [Nat.zero_add, hbytes, update] using htj
      · simp only [Nat.zero_add, hbytes, update, hbyte]
      · exact hf
      · exact hrd
      · exact hwr
      · exact hp0
      · exact h60
      · exact ha0
  | succ n ih =>
    obtain hd1 : InRegions s.wr (s.gpr .a1) 1 := by
      obtain hh := region_offset _ _ _ 0 1 (by decide) (by omega_using []) hd
      simpa only [BitVec.add_zero] using hh
    obtain hs1 : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) 1 := fun x hx hy => hs x hx (by omega_using [hy])
    obtain hctx : ({ table := (contextAt s.mem (s.gpr .a7)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    obtain hstep := apply_step_table s ctx.i ctx.j hcx h7 hal hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, ht6, ha0, hdptr, hcount⟩ := ht
    obtain htail : bytesAt t.mem (s.gpr .a1 + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .a1 + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h7 hal hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    obtain htlen : t.gpr .a2 = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega_using [])
    obtain hpt : InRegions t.wr (t.gpr .a7) 256 := by rw [hwr, hp0]; exact hp
    obtain hdt : InRegions t.wr (t.gpr .a1) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega_using []) hd
    obtain hst : Mem.Sep (t.gpr .a7) 256 (t.gpr .a1) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    obtain htab' : (contextAt t.mem (t.gpr .a7)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega_using [hn]) htab' hti htj (ht6.trans h6)
      (by rw [hp0]; exact hal) htlen hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · rw [Steps.eval_nonzero, hcount, hlen, bne, len_ne n hn]
      rfl
    · have hresult : update ctx (bytesAt s.mem (s.gpr .a1) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .a1) (n + 1))).1,
            (s.mem (s.gpr .a1) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .a1) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        obtain hh : u.mem (s.gpr .a1) = t.mem (s.gpr .a1) := by
          have hf' := hu.frame
          rw [hp0, hdptr] at hf'
          exact stream_head _ _ _ _ _ hn hf' hs
        rw [hh, hbyte, ← hdptr, hu.data]
      · have hf' := hu.frame
        rw [hp0, hdptr] at hf'
        exact stream_frame_trans_tail hf hf'
      · exact hu.rd.trans hrd
      · exact hu.wr.trans hwr
      · exact hu.p.trans hp0
      · exact hu.zero.trans ht6
      · exact hu.ctx.trans ha0

end VG.Proof.Rc4.RISCV64

end

end


/-! # RC4 on RISC-V: the stream function

`apply` copies the table into its frame, runs the stream loop there
(`apply_loop`), copies it back with the PRGA indices, and zeroes the frame. -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

theorem bytes_congr {m m' : Mem} {d : Addr} {n : Nat}
    (h : ∀ i < n, m' (d + BitVec.ofNat 64 i) = m (d + BitVec.ofNat 64 i)) :
    bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- A byte outside the one region of a frame. -/
theorem frame_byte {R : Region} {m m' : Mem} (hf : Frame [R] m m') {x : Addr}
    (hx : ¬ (x - R.base).toNat < R.len) : m' x = m x :=
  hf x fun r hr hc => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hx (by simp only [Region.Contains] at hc; omega_using [hc])

/-- Copying 256 bytes, from `src` to `dst`, separate. -/
theorem copy256_ok (s : State) {src dst : Reg} (hs : Reg.t0 ≠ src) (hd : Reg.t0 ≠ dst)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr src) 256) (hw : InRegions s.wr (s.gpr dst) 256)
    (hsep : Mem.Sep (s.gpr dst) 256 (s.gpr src) 256) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 src dst 0 0 256)) s fun t =>
      (∀ k < 256, t.mem (s.gpr dst + BitVec.ofNat 64 k) = s.mem (s.gpr src + BitVec.ofNat 64 k)) ∧
      Frame [⟨s.gpr dst, 256⟩] s.mem t.mem ∧ (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.mono (Bytes.copyBytes_ok hs hd (by decide) (by decide)
    (fun i hi => by rw [Nat.zero_add]; exact region_offset _ _ _ _ _ (by omega_using [hi]) (by omega_using [hi]) hr)
    (fun i hi => by rw [Nat.zero_add]; exact region_offset _ _ _ _ _ (by omega_using [hi]) (by omega_using [hi]) hw)
    (fun i hi hc => ?_)) fun t ht => ?_
  · simp only [Region.Contains, Nat.zero_add, BitVec.add_zero] at hc
    exact hsep (s.gpr src + BitVec.ofNat 64 i) (by omega_using [hc]) (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]; exact hi)
  · refine ⟨fun k hk => by simpa only [Nat.zero_add] using ht.copied k hk, ?_, ht.gpr, ht.rd,
      ht.wr, ht.sp⟩
    have hf := ht.frame
    simp only [BitVec.add_zero] at hf
    exact hf

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258) :
    WP isa (.block [.load .b .a3 .a0 256, .load .b .t4 .a0 257, .li .t6 0]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .a0 = s.gpr .a0 ∧ t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = s.gpr .a2 ∧
      t.gpr .a3 = (s.mem (s.gpr .a0 + 256#64)).setWidth 64 ∧
      t.gpr .t4 = (s.mem (s.gpr .a0 + 257#64)).setWidth 64 ∧ t.gpr .t6 = 0#64 := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257]

/-- Copying the table back to the context with the PRGA indices, and zeroing
the frame. -/
theorem apply_end (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hF : InRegions s.wr (s.gpr .a7) 256) (hp : InRegions s.wr (s.gpr .a0) 258)
    (hFc : Mem.Sep (s.gpr .a7) 256 (s.gpr .a0) 258) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 .a7 .a0 0 0 256 ++
      ([.store .b .a3 .a0 256, .store .b .t4 .a0 257] : List Instr) ++ wipe)) s fun t =>
      (∀ k < 256, t.mem (s.gpr .a0 + BitVec.ofNat 64 k) = s.mem (s.gpr .a7 + BitVec.ofNat 64 k)) ∧
      t.mem (s.gpr .a0 + 256#64) = (s.gpr .a3).setWidth 8 ∧
      t.mem (s.gpr .a0 + 257#64) = (s.gpr .t4).setWidth 8 ∧
      ∀ x, ¬ (x - s.gpr .a0).toNat < 258 → ¬ (x - s.gpr .a7).toNat < 256 → t.mem x = s.mem x := by
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨region, h, hc⟩ := hF
    exact ⟨region, List.mem_append_right _ h, hc⟩
  obtain hw : InRegions s.wr (s.gpr .a0) 256 := by
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hp
  obtain hsep : Mem.Sep (s.gpr .a0) 256 (s.gpr .a7) 256 := fun x hx hy => hFc x hy (by omega_using [hx])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy256_ok s (by decide) (by decide) hr hw hsep) fun u ⟨uc, uf, ug, urd, uwr, usp⟩ => ?_
  obtain u0 : u.gpr .a0 = s.gpr .a0 := ug _ (by decide)
  obtain u7 : u.gpr .a7 = s.gpr .a7 := ug _ (by decide)
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  obtain hb : WP isa (.block [.store .b .a3 .a0 256, .store .b .t4 .a0 257]) u fun v =>
      v.mem = (u.mem.write (s.gpr .a0 + 256#64) 1 ((s.gpr .a3).setWidth 8)).write
        (s.gpr .a0 + 257#64) 1 ((s.gpr .t4).setWidth 8) ∧ v.gpr = u.gpr ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp := by
    obtain h256' : InRegions u.wr (s.gpr .a0 + BitVec.ofNat 64 256) 1 := by rw [uwr]; exact h256
    obtain h257' : InRegions u.wr (s.gpr .a0 + BitVec.ofNat 64 257) 1 := by rw [uwr]; exact h257
    rrun [h256', h257', u0, ug _ (show Reg.a3 ≠ .t0 by decide), ug _ (show Reg.t4 ≠ .t0 by decide)]
  refine WP.mono hb fun v ⟨vm, vg, vrd, vwr, vsp⟩ => ?_
  obtain v7 : v.gpr .a7 = s.gpr .a7 := by rw [vg, u7]
  refine WP.mono (wipe_ok v (by rw [v7]; exact hal) (by rw [vwr, uwr, v7]; exact hF))
    fun t ⟨tf, _, _, _, _⟩ => ?_
  rw [v7] at tf
  have hne (k : Nat) (hk : k < 256) (e : Nat) (he : 256 ≤ e) (he' : e < 258) :
      s.gpr .a0 + BitVec.ofNat 64 k ≠ s.gpr .a0 + BitVec.ofNat 64 e :=
    Offset.add_ofNat_ne _ (by omega_using [hk]) (by omega_using [he']) (by omega_using [hk, he])
  have hout (k : Nat) (hk : k < 258) : ¬ (s.gpr .a0 + BitVec.ofNat 64 k - s.gpr .a7).toNat < 256 :=
    fun h => hFc _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hk])]; exact hk)
  refine ⟨fun k hk => ?_, ?_, ?_, fun x hx hx' => ?_⟩
  · rw [frame_byte tf (hout k (by omega_using [hk])), vm, write_byte, ite_eq_right (hne k hk 257 (by decide) (by decide)),
      write_byte, ite_eq_right (hne k hk 256 (by decide) (by decide)), uc k hk]
  · rw [frame_byte tf (hout 256 (by decide)), vm, write_byte,
      ite_eq_right (Offset.add_ofNat_ne _ (by decide) (by decide) (by decide)), write_byte, ite_eq_left rfl]
  · rw [frame_byte tf (hout 257 (by decide)), vm, write_byte, ite_eq_left rfl]
  · have h1 : x ≠ s.gpr .a0 + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    obtain h2 : x ≠ s.gpr .a0 + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [frame_byte tf hx', vm, write_byte, ite_eq_right h2, write_byte, ite_eq_right h1,
      frame_byte uf (by simp only; omega_using [hx])]

/-- `applyMain`, with its frame at the stack pointer, from the PRGA indices
loaded. -/
theorem apply_main (s : State) (n : Nat) (hbound : n + 1 < 2 ^ 64)
    (hlen : s.gpr .a2 = BitVec.ofNat 64 (n + 1))
    (h3 : s.gpr .a3 = (s.mem (s.gpr .a0 + 256#64)).setWidth 64)
    (h4 : s.gpr .t4 = (s.mem (s.gpr .a0 + 257#64)).setWidth 64) (h6 : s.gpr .t6 = 0#64)
    (hal : s.sp.toNat % 8 = 0) (hF : InRegions s.wr s.sp 256)
    (hp : InRegions s.wr (s.gpr .a0) 258)
    (hd : InRegions s.wr (s.gpr .a1) (n + 1))
    (hs : Mem.Sep (s.gpr .a0) 258 (s.gpr .a1) (n + 1))
    (hFc : Mem.Sep s.sp 256 (s.gpr .a0) 258)
    (hFd : Mem.Sep s.sp 256 (s.gpr .a1) (n + 1)) :
    WP isa applyMain s fun t =>
      let result := update (contextAt s.mem (s.gpr .a0)) (bytesAt s.mem (s.gpr .a1) (n + 1))
      contextAt t.mem (s.gpr .a0) = result.1 ∧ bytesAt t.mem (s.gpr .a1) (n + 1) = result.2 := by
  obtain hpRead : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold applyMain
  refine WP.seq (Wp.wp_addSp (by decide) fun b hb => ?_)
  obtain b7 : b.gpr .a7 = s.sp := by rw [hb.gpr, BitVec.add_zero]
  obtain b0 : b.gpr .a0 = s.gpr .a0 := hb.other _ (by decide)
  obtain hbr : InRegions (b.rd ++ b.wr) (b.gpr .a0) 256 := by
    rw [hb.rd, hb.wr, b0]
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hpRead
  refine WP.mono (copy256_ok b (src := .a0) (dst := .a7) (by decide) (by decide) hbr
    (by rw [hb.wr, b7]; exact hF)
    (by rw [b7, b0]; exact fun x hx hy => hFc x hx (by omega_using [hy])))
    fun c ⟨cc, cf, cg, crd, cwr, csp⟩ => ?_
  rw [b7, b0, hb.mem] at cc
  rw [b7, hb.mem] at cf
  obtain c7 : c.gpr .a7 = s.sp := (cg _ (by decide)).trans b7
  obtain c0 : c.gpr .a0 = s.gpr .a0 := (cg _ (by decide)).trans b0
  obtain c1 : c.gpr .a1 = s.gpr .a1 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c2 : c.gpr .a2 = s.gpr .a2 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c3 : c.gpr .a3 = s.gpr .a3 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c4 : c.gpr .t4 = s.gpr .t4 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c6 : c.gpr .t6 = s.gpr .t6 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain cw : c.wr = s.wr := by rw [cwr, hb.wr]
  obtain hdata : bytesAt c.mem (s.gpr .a1) (n + 1) = bytesAt s.mem (s.gpr .a1) (n + 1) :=
    bytes_congr fun i hi => frame_byte cf fun h =>
      hFd _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hbound, hi])]; exact hi)
  let ctx := contextAt s.mem (s.gpr .a0)
  refine WP.seq (WP.mono (apply_loop n c ctx hbound
    (by rw [c7]; exact table_copy cc) (c3.trans h3) (c4.trans h4) (c6.trans h6)
    (by rw [c7]; exact hal) (c2.trans hlen)
    (by rw [cw, c7]; exact hF) (by rw [cw, c1]; exact hd) (by rw [c7, c1]; exact hFd))
    fun e he => ?_)
  obtain e7 : e.gpr .a7 = s.sp := he.p.trans c7
  obtain e0 : e.gpr .a0 = s.gpr .a0 := he.ctx.trans c0
  obtain ew : e.wr = s.wr := he.wr.trans cw
  refine WP.mono (apply_end e (by rw [e7]; exact hal) (by rw [ew, e7]; exact hF)
    (by rw [ew, e0]; exact hp) (by rw [e7, e0]; exact hFc)) fun t ⟨ttab, ti, tj, tout⟩ => ?_
  rw [e0, e7] at ttab
  rw [e0] at ti tj tout
  rw [e7] at tout
  have htab := he.table
  have hi := he.i
  have hj := he.j
  have hdat := he.data
  rw [c7] at htab
  rw [c1, hdata] at htab hi hj hdat
  refine ⟨context_of (by rw [table_copy ttab, htab]) (by rw [ti, hi, low_byte])
    (by rw [tj, hj, low_byte]), ?_⟩
  rw [← hdat]
  exact bytes_congr fun i hi => tout _
    (fun h => hs _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hbound, hi])]; exact hi))
    (fun h => hFd _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hbound, hi])]; exact hi))

/-- The stream function, in its frame of 256 bytes below the stack pointer. -/
theorem apply_ok (s : State) (hal : s.sp.toNat % 16 = 0) (hsp : 256 ≤ s.sp.toNat)
    (hp : InRegions s.wr (s.gpr .a0) 258)
    (hd : InRegions s.wr (s.gpr .a1) (s.gpr .a2).toNat)
    (hs : Mem.Sep (s.gpr .a0) 258 (s.gpr .a1) (s.gpr .a2).toNat)
    (hFc : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a0) 258)
    (hFd : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a1) (s.gpr .a2).toNat) :
    WP isa VG.Impl.Rc4.RISCV64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .a0))
        (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
      contextAt t.mem (s.gpr .a0) = result.1 ∧
        bytesAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = result.2 := by
  obtain hpRead : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.RISCV64.apply
  refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, hasp, ha0, ha1, ha2, ha3, ha4, ha6⟩ := ha
  refine WP.ite (s.gpr .a2 == 0) (by rw [Steps.eval_zero, ha2]) (fun hz => ?_) (fun hnz => ?_)
  · have hz' : s.gpr .a2 = 0 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨context_ext rfl rfl rfl, rfl⟩
  · have hnz' : s.gpr .a2 ≠ 0 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .a2).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .a2).toNat = n + 1 at hnEq
    obtain hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .a2).isLt
    rw [hnEq]
    rw [hnEq] at hd hs hFd
    obtain hF : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsp])]; rfl
    refine WP.allocKept (n := frameBytes) (by decide) (by rw [hasp]; exact hsp) ?_
    obtain hsp' : (allocd frameBytes a).sp = s.sp - 256#64 := by
      show a.sp - BitVec.ofNat 64 256 = _
      rw [hasp]
    have hg : (allocd frameBytes a).gpr = a.gpr := rfl
    have hm : (allocd frameBytes a).mem = a.mem := rfl
    obtain hw : (allocd frameBytes a).wr = ⟨s.sp - 256#64, 256⟩ :: s.wr := by
      show (⟨a.sp - BitVec.ofNat 64 256, 256⟩ :: a.wr : List Region) = _
      rw [hasp, haw]
    have hwr (r : Region) (h : r ∈ s.wr) : r ∈ (allocd frameBytes a).wr := by
      rw [hw]; exact List.mem_cons_of_mem _ h
    refine WP.mono (apply_main (allocd frameBytes a) n hbound
      (by rw [hg, ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [hg, hm, ha3, ha0, ham]) (by rw [hg, hm, ha4, ha0, ham]) (by rw [hg, ha6])
      (by rw [hsp', hF]; omega_using [hal])
      ⟨⟨s.sp - 256#64, 256⟩, by rw [hw]; exact List.mem_cons_self,
        by rw [hsp']; exact Region.contains_self _ _⟩
      (by obtain ⟨r, hr, hc⟩ := hp; exact ⟨r, hwr r hr, by rw [hg, ha0]; exact hc⟩)
      (by obtain ⟨r, hr, hc⟩ := hd; exact ⟨r, hwr r hr, by rw [hg, ha1]; exact hc⟩)
      (by rw [hg, ha0, ha1]; exact hs) (by rw [hsp', hg, ha0]; exact hFc)
      (by rw [hsp', hg, ha1]; exact hFd)) fun u hu => ?_
    rw [hg, hm, ha0, ha1, ham] at hu
    exact hu

end VG.Proof.Rc4.RISCV64
