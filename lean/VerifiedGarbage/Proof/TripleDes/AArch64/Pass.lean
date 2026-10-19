module

public import VerifiedGarbage.Proof.TripleDes.AArch64.PassStart
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

theorem swapHalves_noV : swapHalves.all (fun i => vdstOf i == none) = true := by decide

theorem passCountAdvance_ok (s : State) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      passesOf s' = passesOf s - 1 ∧ s'.gpr .x3 = passesOf s - 1 ∧
      (∀ w, w ≠ .v1 → s'.v w = s.v w) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .x .x3 (vdword (s.v .v1) 0)
  let s₂ := s₁.write .x .x3 (s₁.read .x .x3 - BitVec.ofNat _ 1)
  let s₃ := s₂.setV .v1 (ofVDwords (s₂.gpr .x3) (s₂.gpr .x3))
  have h3 : s₂.gpr .x3 = passesOf s - 1 := by
    simp only [s₂, s₁, State.read, BitVec.setWidth_eq, gpr_write, ite_true, passesOf]
    rfl
  refine ⟨s₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [passCountAdvance, runBlock_cons, show exec (.umov .x .x3 .v1 0) s = some s₁ from rfl,
      runStep_some, runBlock_cons, VG.AArch64.exec_subImm_x (by decide), runStep_some,
      runBlock_cons, show exec (.vop (.dup .d2 .v1 .x3)) s₂ = some s₃ from rfl, runStep_some,
      runBlock_nil]
  · rw [passesOf, v_setV_self, VG.AArch64.vdword_ofVDwords_0, h3]
  · simp only [s₃, gpr_setV, h3]
  · intro w hw
    exact v_setV_of_ne (s := s₂) _ hw
  · simp only [s₃, s₂, s₁, mem_setV, mem_write]
  · simp only [s₃, s₂, s₁, rd_setV, rd_write]
  · simp only [s₃, s₂, s₁, wr_setV, wr_write]
  · simp only [s₃, s₂, s₁, sp_setV, sp_write]
  · intro r hr
    simp only [s₃, s₂, s₁, gpr_setV, gpr_write, hr, ite_false]

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr .x22 = s.gpr .x0 + BitVec.ofNat 64 (passOffset c d)
  count : t.gpr .x21 = BitVec.ofNat 64 16
  mem : t.mem = s.mem
  step : stepOf t = stepVal d
  vec : ∀ w, w ≠ .v0 → t.v w = s.v w
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x21 → r ≠ .x22 → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : passesOf s = BitVec.ofNat 64 p) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  have branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.v = s.v → t.rd = s.rd →
      t.wr = s.wr → t.sp = s.sp → (∀ r, r ≠ .x3 → r ≠ .x4 → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hv hrd hwr hsp hg
    subst hq
    obtain ⟨u, run, ptr, count, mem, step, vec, rd, wr, sp, regs⟩ := passStart_ok (passOf d q).1
      (passOf_lt d q) (passOf d q).2 t
    refine WP.of_runBlock ⟨u, run, ?_, count, mem.trans hm, step, ?_, rd.trans hrd, wr.trans hwr,
      sp.trans hsp, ?_⟩
    · rw [ptr, hg .x0 (by decide) (by decide)]
    · intro w hw
      rw [vec w hw, hv]
    · intro r h3 h4 h21 h22
      exact (regs r h3 h21 h22).trans (hg r h3 h4)
  let s₁ := s.write .x .x3 (vdword (s.v .v1) 0)
  let t₁ := s₁.write .x .x4 (s₁.read .x .x3 - BitVec.ofNat _ 3)
  have hx3 : t₁.gpr .x3 = BitVec.ofNat 64 p := by
    simp only [t₁, s₁, gpr_write, reduceCtorEq, ite_false, ite_true]
    exact hpasses
  have hg₁ : ∀ r, r ≠ .x3 → r ≠ .x4 → t₁.gpr r = s.gpr r := by
    intro r h3 h4
    simp only [t₁, s₁, gpr_write, h3, h4, ite_false]
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by
    rw [runBlock_cons, show exec (.umov .x .x3 .v1 0) s = some s₁ from rfl, runStep_some,
      runBlock_cons, VG.AArch64.exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have zf₁ : isa.eval (.zero .x .x4) t₁ = some (p == 3) := by
    change VG.AArch64.eval (.zero .x .x4) t₁ = _
    simp only [VG.AArch64.eval, State.read, BitVec.setWidth_eq, t₁, gpr_write, ite_true]
    rw [show s₁.gpr .x3 = BitVec.ofNat 64 p from hx3]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm rfl rfl rfl rfl rfl hg₁
  · intro h3
    apply WP.seq
    let t₂ := t₁.write .x .x4 (t₁.read .x .x3 - BitVec.ofNat _ 2)
    refine WP.of_runBlock ⟨t₂, by
      rw [runBlock_cons, VG.AArch64.exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
    have zf₂ : isa.eval (.zero .x .x4) t₂ = some (p == 2) := by
      change VG.AArch64.eval (.zero .x .x4) t₂ = _
      simp only [VG.AArch64.eval, State.read, BitVec.setWidth_eq, t₂, gpr_write, ite_true, hx3]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    have hg₂ : ∀ r, r ≠ .x3 → r ≠ .x4 → t₂.gpr r = s.gpr r := by
      intro r h3 h4
      simp only [t₂, gpr_write, h4, ite_false]
      exact hg₁ r h3 h4
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm rfl rfl rfl rfl rfl hg₂
    · intro h2
      have hp3 : p ≠ 3 := by simpa using h3
      have hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega) rfl rfl rfl rfl rfl hg₂

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr .x19 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .x20 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem
  passes : passesOf s = BitVec.ofNat 64 (n - 1)
  zf : isa.eval (.nonzero .x .x3) s = some (decide (n ≠ 1))

/-- A complete DES pass: the choice of its keys by the passes left, its
sixteen rounds, the final half swap and the passes left counted down. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .x19 = v.1.setWidth 64) (hr : origin.gpr .x20 = v.2.setWidth 64)
    (hpasses : passesOf origin = BitVec.ofNat 64 p)
    (hptr : origin.gpr .x0 + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr base (passOf d p).2 0)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base (passOf d p).2 j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base (passOf d p).2 j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base (passOf d p).2 j) 64).setWidth 48 =
      roundKey keys (passOf d p).2 j) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses) fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hread hsep hkeys ⊢
  have hbase : s.gpr .x2 = origin.gpr .x2 := hs.regs .x2 (by decide) (by decide) (by decide)
    (by decide)
  have hspill : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hloop := roundsLoop_ok keys dir base s v
    (hok.congr hbase hbase hs.rd hs.wr)
    ((hs.regs .x19 (by decide) (by decide) (by decide) (by decide)).trans hl)
    ((hs.regs .x20 (by decide) (by decide) (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hs.count hs.step
    (by rw [hs.rd, hs.wr]; exact hread)
    (by rw [hspill]; exact hsep) (by rw [hs.mem]; exact hkeys)
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, sp₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  have v₃ : s₃.v = s₂.v := VG.AArch64.Tbl.runBlock_v swapHalves_noV run₃
  obtain ⟨s₄, run₄, p₄, x3₄, v₄, mem₄, rd₄, wr₄, sp₄, regs₄⟩ := passCountAdvance_ok s₃
  have hp₃ : passesOf s₃ = BitVec.ofNat 64 p := by
    rw [passesOf, v₃, hs₂.vec, hs.vec .v1 (by decide)]
    exact hpasses
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), sp₄.trans (sp₃.trans (hs₂.sp.trans hs.sp)),
    ?_, ?_, ?_, ?_⟩
  · exact (regs₄ .x19 (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ .x20 (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hne : q ≠ .x3 ∧ q ≠ .x4 ∧ q ≠ .x21 ∧ q ≠ .x22 := by revert hq; cases q <;> decide
    exact (regs₄ q hne.1).trans ((regs₃ q hq').trans ((hs₂.regs q hq).trans
      (hs.regs q hne.1 hne.2.1 hne.2.2.1 hne.2.2.2)))
  · have hf := hs₂.frame
    rw [hspill, hs.mem] at hf
    rw [mem₄, mem₃]
    exact hf
  · rw [p₄, hp₃, hsub]
  · change VG.AArch64.eval (.nonzero .x .x3) s₄ = some (decide (p ≠ 1))
    simp only [VG.AArch64.eval, State.read, BitVec.setWidth_eq, x3₄, hp₃]
    rw [hsub]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide

end VG.Proof.TripleDes.AArch64
