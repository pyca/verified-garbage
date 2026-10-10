import VerifiedGarbage.Impl.Ed448.AArch64.Point56
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Ed448 on AArch64: field code as a function

Untrusted: everything here is checked by Lean. `asFn_ok`: code that writes no
lane where `asFn` keeps the callee-saved registers (`keptRegs`), run as a
function, starts from `ws` in `x3` and the mask in `x12`, and ends with every
register it keeps (outside `rs`) or that `asFn` keeps restored. The lanes are
set by `insOf_ok`, kept by the code (`Exec.vec`), and read back by `umovOf_ok`.
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- The instructions keeping registers in lanes. -/
def insOf (ks : List (Reg × VReg × Nat)) : List Instr := ks.map fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)

/-- The instructions restoring them. -/
def umovOf (ks : List (Reg × VReg × Nat)) : List Instr := ks.map fun k => .umov .x k.1 k.2.1 k.2.2

theorem exec_ins {s : State} {r : Reg} {v : VReg} {l : Nat} (hl : l < 2) :
    exec (.vop (.ins .d2 v l r)) s = some (s.setV v (setLane (s.v v) 64 l (s.gpr r))) := by
  simp only [exec, VOp.eval, hl, ite_true, Option.map_some]

theorem exec_umov {s : State} {r : Reg} {v : VReg} {l : Nat} (hl : l < 2) :
    exec (.umov .x r v l) s = some (s.write .x r (laneOf s v l)) := by
  have : 64 * l < 128 := by omega
  simp only [exec, Size.bits, laneOf, Nat.mul_comm l 64, this, ite_true]

theorem laneOf_setV {s : State} {v w : VReg} {x : BitVec 128} {l : Nat} :
    laneOf (s.setV v x) w l = if w = v then x.extractLsb' (64 * l) 64 else laneOf s w l := by
  simp only [laneOf, RegUpd.v_setV]
  split <;> rfl

/-- Keeping the registers of `ks` in their lanes, distinct and below 2. -/
theorem insOf_ok : ∀ (ks : List (Reg × VReg × Nat)) (s : State), (∀ k ∈ ks, k.2.2 < 2) →
    (ks.map fun k => (k.2.1, k.2.2)).Nodup →
    WP isa (.block (insOf ks)) s fun t => t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ (∀ k ∈ ks, laneOf t k.2.1 k.2.2 = s.gpr k.1) ∧
      ∀ v l, l < 2 → (v, l) ∉ ks.map (fun k => (k.2.1, k.2.2)) → laneOf t v l = laneOf s v l
  | [], s, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, by simp, fun _ _ _ _ => rfl⟩
  | k :: ks, s, hl, hn => by
    have hk := hl k List.mem_cons_self
    refine WP.block_cons_iff.mpr ⟨_, exec_ins hk, ?_⟩
    obtain ⟨hn₁, hn₂⟩ := List.nodup_cons.mp hn
    refine WP.mono (insOf_ok ks _ (fun k' h => hl k' (List.mem_cons_of_mem _ h)) hn₂)
      fun t ⟨hg, hm, hr, hw, hsp, hls, hoth⟩ => ?_
    have lane : ∀ v l, l < 2 →
        laneOf (s.setV k.2.1 (setLane (s.v k.2.1) 64 k.2.2 (s.gpr k.1))) v l =
          if v = k.2.1 ∧ l = k.2.2 then s.gpr k.1 else laneOf s v l := fun v l hl' => by
      rw [laneOf_setV]
      by_cases hv : v = k.2.1
      · subst hv
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), extract_setLane64 _ _ hk hl']
        by_cases hll : k.2.2 = l
        · subst hll; simp
        · simp only [hll, ite_false, laneOf, true_and, Ne.symm hll]
      · simp [hv]
    refine ⟨hg, hm, hr, hw, hsp, fun k' hk' => ?_, fun v l hl' hvl => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hoth _ _ hk hn₁, lane _ _ hk, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩)]
      · rw [hls k' hk', RegUpd.gpr_setV]
    · simp only [List.map_cons, List.mem_cons, not_or] at hvl
      rw [hoth v l hl' hvl.2, lane v l hl', ite_eq_right_of_eq_false _ _ (eq_false fun h => hvl.1 (by rw [h.1, h.2]))]

/-- Restoring the registers of `ks`, distinct, from their lanes. -/
theorem umovOf_ok : ∀ (ks : List (Reg × VReg × Nat)) (s : State), (∀ k ∈ ks, k.2.2 < 2) →
    (ks.map Prod.fst).Nodup →
    WP isa (.block (umovOf ks)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ k ∈ ks, t.gpr k.1 = laneOf s k.2.1 k.2.2) ∧ ∀ r, r ∉ ks.map Prod.fst → t.gpr r = s.gpr r
  | [], s, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, by simp, fun _ _ => rfl⟩
  | k :: ks, s, hl, hn => by
    have hk := hl k List.mem_cons_self
    refine WP.block_cons_iff.mpr ⟨_, exec_umov hk, ?_⟩
    obtain ⟨hn₁, hn₂⟩ := List.nodup_cons.mp hn
    refine WP.mono (umovOf_ok ks _ (fun k' h => hl k' (List.mem_cons_of_mem _ h)) hn₂)
      fun t ⟨hm, hr, hw, hsp, hls, hoth⟩ => ?_
    have hlane : ∀ v l, laneOf (s.write .x k.1 (laneOf s k.2.1 k.2.2)) v l = laneOf s v l := fun _ _ => rfl
    refine ⟨hm, hr, hw, hsp, fun k' hk' => ?_, fun r hr' => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hoth _ hn₁, RegUpd.gpr_write_self]; rfl
      · rw [hls k' hk', hlane]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr'
      rw [hoth r hr'.2, RegUpd.gpr_write_of_ne _ _ _ hr'.1]

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
