module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Spills
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.TripleDes.Word

/-! ### `TripleDes.AArch64.Pass`, which only this module used -/

section

/-! ### `TripleDes.AArch64.PassStart`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Loop`, which only this module used -/

section

/-! ### `TripleDes.AArch64.RoundStep`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def roundStepKept : List Reg := [.x0, .x1, .x2, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) != 0) = decide (n ≠ 1) := by
  decide +kernel

/-- The key step of the pass, in the low lane of `v0`. -/
def stepOf (s : State) : BitVec 64 := vdword (s.v .v0) 0

/-- The passes left, in the low lane of `v1`. -/
def passesOf (s : State) : BitVec 64 := vdword (s.v .v1) 0

theorem roundBody_noV : roundBody.all (fun i => vdstOf i == none) = true := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr .x22 = s.gpr .x22 + stepOf s ∧
      s'.gpr .x21 = s.gpr .x21 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.v = s.v ∧
      (∀ r, r ≠ .x3 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .x .x3 (vdword (s.v .v0) 0)
  let s₂ := s₁.write .x .x22 (s₁.read .x .x22 + s₁.read .x .x3)
  let s₃ := s₂.write .x .x21 (s₂.read .x .x21 - BitVec.ofNat _ 1)
  refine ⟨s₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, show exec (.umov .x .x3 .v0 0) s = some s₁ from rfl,
      runStep_some, runBlock_cons, VG.AArch64.exec_add, runStep_some, runBlock_cons,
      VG.AArch64.exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, stepOf, State.read, BitVec.setWidth_eq, gpr_write, reduceCtorEq,
      ite_true, ite_false]
  · simp only [s₃, s₂, s₁, State.read, BitVec.setWidth_eq, gpr_write, reduceCtorEq,
      ite_true, ite_false]
    rfl
  · simp only [s₃, s₂, s₁, rd_write]
  · simp only [s₃, s₂, s₁, wr_write]
  · simp only [s₃, s₂, s₁, sp_write]
  · simp only [s₃, s₂, s₁, mem_write]
  · intro r hr₁ hr₂ hr₃
    simp only [s₃, s₂, s₁, gpr_write, hr₁, hr₂, hr₃, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .x22) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8)
    (hsep : (⟨s.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .x21 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr .x19 = r.setWidth 64 ∧
      s'.gpr .x20 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .x22 = s.gpr .x22 + stepOf s ∧ s'.v = s.v ∧
      s'.gpr .x21 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero .x .x21) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, sp₂, mem₂, v₂, keep₂⟩ := roundAdvance_ok s₁
  have v₁ : s₁.v = s.v := VG.AArch64.Tbl.runBlock_v roundBody_noV run₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .x21 = BitVec.ofNat 64 n := (keep₁ .x21 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, v₂.trans v₁, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁,
    ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .x19 (by decide) (by decide) (by decide)).trans left₁
  · exact (keep₂ .x20 (by decide) (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .x22 (by decide), stepOf, stepOf, v₁]
  · rw [count₂, hcount₁, hsub]
  · change VG.AArch64.eval (.nonzero .x .x21) s₂ = _
    simp only [VG.AArch64.eval, State.read, BitVec.setWidth_eq, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .x3 ∧ q ≠ .x21 ∧ q ≠ .x22 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2.1 hneq.2.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

/-- The key step of a pass, in the low lane of `v0`. -/
def stepVal (direction : Direction) : BitVec 64 := if direction = .encrypt then 8 else -8

theorem keyAddr_step (base : Addr) (direction : Direction) (j : Nat) (hj : j < 15) :
    keyAddr base direction j + stepVal direction = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega_using [])
  · change base + BitVec.ofNat 64 (8 * (15 - j)) + -BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (15 - (j + 1)))
    rw [← BitVec.sub_eq_add_neg, Offset.add_ofNat_sub _ (by omega_using [hj])]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega_using [])

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .x19 = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr .x20 = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.gpr .x21 = BitVec.ofNat 64 n
  pointer : s.gpr .x22 = keyAddr base direction (16 - n)
  step : stepOf s = stepVal direction
  vec : s.v = origin.v
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .x19 = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr .x20 = (roundPrefix keys direction 16 v).2.setWidth 64
  counter : s.gpr .x21 = 0
  vec : s.v = origin.v
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance)) s (fun s' =>
      (isa.eval (.nonzero .x .x21) s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval (.nonzero .x .x21) s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : spillRegion s = spillRegion origin := by
    simp only [spillRegion, hs.regs .x2 (by decide)]
  have hokS : Ok sboxCfg s := hok.congr
    (hs.regs .x2 (by decide)) (hs.regs .x2 (by decide)) hs.rd hs.wr
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hsepS : (⟨s.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s) := by
    rw [hs.pointer]
    rw [hwork]
    exact hsep _ hj
  have hk : (s.mem.readW (s.gpr .x22) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer]
    have hmem := hs.frame.readW (a := keyAddr base direction (16 - n)) (w := 64)
      (r := ⟨keyAddr base direction (16 - n), 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact hsep _ hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, vec, count, flag, rd, wr, sp, regs, frame⟩ :=
    roundStep_ok s _ _ (s.mem.readW (s.gpr .x22) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .x19 = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .x20 = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : Frame [spillRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, vec.trans hs.vec, rd.trans hs.rd, wr.trans hs.wr,
        sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, by rw [stepOf, vec]; exact hs.step, vec.trans hs.vec,
        rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, hs.step, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .x19 = v.1.setWidth 64) (hr : origin.gpr .x20 = v.2.setWidth 64)
    (hptr : origin.gpr .x22 = keyAddr base direction 0)
    (hcount : origin.gpr .x21 = BitVec.ofNat 64 16)
    (hstep : stepOf origin = stepVal direction)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance)) (.nonzero .x .x21))
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance))
    (c := .nonzero .x .x21) (Q := LoopPost keys direction origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, hstep, rfl, rfl, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 4096 := by
  intro c hc d
  cases d <;> simp only [passOffset, reduceCtorEq, ite_true, ite_false] <;> omega_using [hc]

theorem stepVal_eq (s : State) (d : Direction) :
    (if d = .encrypt then s.gpr .x0 - s.gpr .x0 + BitVec.ofNat 64 8
      else s.gpr .x0 - s.gpr .x0 - BitVec.ofNat 64 8) = stepVal d := by
  cases d <;> simp [stepVal, BitVec.sub_self] <;> rfl

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .x22 = s.gpr .x0 + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr .x21 = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      stepOf s' = stepVal direction ∧ (∀ w, w ≠ .v0 → s'.v w = s.v w) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  change 128 * component + (if direction = .encrypt then 0 else 120) < 4096 at hb
  let s₁ := s.write .x .x22 (s.read .x .x0 +
    BitVec.ofNat _ (128 * component + if direction = .encrypt then 0 else 120))
  let s₂ := s₁.write .x .x21 ((BitVec.ofNat 16 16).setWidth 64)
  let s₃ := s₂.write .x .x3 (s₂.read .x .x0 - s₂.read .x .x0)
  let s₄ := s₃.write .x .x3 (if direction = .encrypt then s₃.read .x .x3 + BitVec.ofNat _ 8
    else s₃.read .x .x3 - BitVec.ofNat _ 8)
  let s₅ := s₄.setV .v0 (ofVDwords (s₄.gpr .x3) (s₄.gpr .x3))
  have h3 : s₄.gpr .x3 = stepVal direction := by
    rw [← stepVal_eq s direction]
    cases direction <;>
      simp only [s₄, s₃, s₂, s₁, State.read, BitVec.setWidth_eq, gpr_write, reduceCtorEq,
        ite_true, ite_false]
  have e₄ : exec (if direction = .encrypt then .addImm .x .x3 .x3 8 else .subImm .x .x3 .x3 8)
      s₃ = some s₄ := by
    cases direction
    · exact VG.AArch64.exec_addImm_x (by decide)
    · exact VG.AArch64.exec_subImm_x (by decide)
  refine ⟨s₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [passStart, runBlock_cons, VG.AArch64.exec_addImm_x hb, runStep_some, runBlock_cons, imm,
      show exec (.movz .x .x21 (BitVec.ofNat 16 16) 0) s₁ = some s₂ from rfl, runStep_some,
      runBlock_cons, show exec (.sub .x .x3 .x0 .x0) s₂ = some s₃ from rfl, runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_cons,
      show exec (.vop (.dup .d2 .v0 .x3)) s₄ = some s₅ from rfl, runStep_some, runBlock_nil]
  · simp only [s₅, s₄, s₃, s₂, s₁, State.read, BitVec.setWidth_eq, gpr_setV, gpr_write,
      reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, mem_setV, mem_write]
  · rw [stepOf, v_setV_self, VG.AArch64.vdword_ofVDwords_0, h3]
  · intro w hw
    exact v_setV_of_ne (s := s₄) _ hw
  · simp only [s₅, s₄, s₃, s₂, s₁, rd_setV, rd_write]
  · simp only [s₅, s₄, s₃, s₂, s₁, wr_setV, wr_write]
  · simp only [s₅, s₄, s₃, s₂, s₁, sp_setV, sp_write]
  · intro r hr₁ hr₂ hr₃
    simp only [s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, hr₁, hr₂, hr₃, ite_false]

end VG.Proof.TripleDes.AArch64

end

end


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
      exact branch t₂ 1 (by omega_using [hp, hp3, hp2]) rfl rfl rfl rfl rfl hg₂

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
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega_using [hp]) hp.1
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

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .x19 = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr .x20 = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : State} {x : BitVec 64} {n : Nat}
    (hs : PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) n s) :
    WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32).setWidth 64 = halves.2.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_left halves.2 halves.1))
  have hright : ((desCore keys direction x).setWidth 32).setWidth 64 = halves.1.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_right halves.2 halves.1))
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.AArch64
