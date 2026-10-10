import VerifiedGarbage.Impl.Ed448.AArch64.Point56
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Ed448 on AArch64: field code as a function

Untrusted: everything here is checked by Lean. `asFn_ok`: code that writes no
lane where `asFn` keeps the callee-saved registers (`keptRegs`), run as a
function, starts from `ws` in `x3` and the mask in `x12`, and ends with every
register it keeps (outside `rs`) or that `asFn` keeps restored. The lanes are
set by `insOf_ok`, kept by the code (`Exec.vec`), and read back by `umovOf_ok`
(`Proof/Framework/AArch64/LaneSave.lean`).
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- `x3 := x0` (the working space) and `x12 := 2²⁸ - 1`. -/
theorem regs_ok (s : State) :
    WP isa (.block ([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x12 = 0x0fffffff ∧
        (∀ r, r ≠ .x3 → r ≠ .x12 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by decide, fun r h3 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [h3, h12, ite_false]

theorem keptRegs_lanes (c : Bool) : ∀ k ∈ keptRegs c, k.2.2 < 2 := by cases c <;> decide

theorem keptRegs_nodup_lanes (c : Bool) : ((keptRegs c).map fun k => (k.2.1, k.2.2)).Nodup := by
  cases c <;> decide

theorem keptRegs_nodup (c : Bool) : ((keptRegs c).map Prod.fst).Nodup := by cases c <;> decide

/-- `body` as a function: from `s`, `body` runs with `ws` (from `x0`) in `x3`, the mask in
`x12` and every other register as in `s`; if it changes no register outside `rs` (which holds
neither `x3` nor `x12`) and no lane `asFn` keeps registers in, and ends in memory satisfying `Q`,
then so does `asFn c body`, which keeps every register outside `rs`, or kept, but `x3` and
`x12`, and leaves `ws` in `x3` and the mask in `x12`. -/
theorem asFn_ok {c : Bool} {body : Prog isa} {rs : List Reg} {s : State} {Q : Mem → Prop}
    (h3 : .x3 ∉ rs) (h12 : .x12 ∉ rs)
    (hv : body.allInstrs (fun i => (keptRegs c).all fun k => vdstOf i != some k.2.1) = true)
    (hbody : ∀ s₁ : State, s₁.gpr .x3 = s.gpr .x0 → s₁.gpr .x12 = 0x0fffffff →
      (∀ r, r ≠ .x3 → r ≠ .x12 → s₁.gpr r = s.gpr r) → s₁.mem = s.mem → s₁.rd = s.rd →
      s₁.wr = s.wr → WP isa body s₁ fun t =>
        (∀ r, r ∉ rs → t.gpr r = s₁.gpr r) ∧ t.rd = s₁.rd ∧ t.wr = s₁.wr ∧ Q t.mem) :
    WP isa (asFn c body) s fun u =>
      (∀ r, (r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst) → r ≠ .x3 → r ≠ .x12 → u.gpr r = s.gpr r) ∧
      u.gpr .x3 = s.gpr .x0 ∧ u.gpr .x12 = 0x0fffffff ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Q u.mem := by
  unfold asFn
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (regs_ok s) fun s₀ ⟨g3, g12, gk, gm, gr, gw, gsp, gv⟩ => ?_
  refine WP.mono (insOf_ok (keptRegs c) s₀ (keptRegs_lanes c) (keptRegs_nodup_lanes c))
    fun s₁ ⟨hg, hm, hr, hw, hsp, hls, _⟩ => ?_
  rw [WP.seq_iff]
  obtain ⟨tb, t, he, hk, htr, htw, hq⟩ := hbody s₁ (by rw [hg, g3]) (by rw [hg, g12])
    (fun r h3' h12' => by rw [hg, gk r h3' h12']) (hm.trans gm) (hr.trans gr) (hw.trans gw)
  refine ⟨tb, t, he, ?_⟩
  have tl : ∀ k ∈ keptRegs c, laneOf t k.2.1 k.2.2 = s.gpr k.1 := fun k hk' => by
    have hk3 : ∀ k ∈ keptRegs c, k.1 ≠ .x3 ∧ k.1 ≠ .x12 := by cases c <;> decide
    have hv' : ∀ i ∈ instrs body, vdstOf i ≠ some k.2.1 := fun i hi => by
      rw [Code.allInstrs_eq] at hv
      have := List.all_eq_true.mp (List.all_eq_true.mp hv i hi) k hk'
      simpa using this
    rw [laneOf, Exec.vec hv' he, ← laneOf, hls k hk', gk _ (hk3 k hk').1 (hk3 k hk').2]
  refine WP.mono (umovOf_ok (keptRegs c) t (keptRegs_lanes c) (keptRegs_nodup c))
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  have kept3 : .x3 ∉ (keptRegs c).map Prod.fst := by cases c <;> decide
  have kept12 : .x12 ∉ (keptRegs c).map Prod.fst := by cases c <;> decide
  have t3 : t.gpr .x3 = s₁.gpr .x3 := hk _ h3
  have t12 : t.gpr .x12 = s₁.gpr .x12 := hk _ h12
  refine ⟨fun r hr' h3' h12' => ?_, by rw [uoth _ kept3, t3, hg, g3], by rw [uoth _ kept12, t12, hg, g12],
    by rw [ur, htr, hr, gr], by rw [uw, htw, hw, gw], by rw [usp, Exec.sp he, hsp, gsp], by rw [um]; exact hq⟩
  by_cases hm' : r ∈ (keptRegs c).map Prod.fst
  · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hm'
    rw [uls k hk', tl k hk']
  · rw [uoth r hm', hk r (hr'.resolve_right hm'), hg, gk r h3' h12']

end VG.Proof.Ed448.AArch64.Point56
