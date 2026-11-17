module

public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.TripleDes.AArch64.Box
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/-! ### `TripleDes.AArch64.Pre`, which this module and modules that import it used -/

section

/-! ### `TripleDes.AArch64.Ready`, which only this module used -/

section

/-! ### `TripleDes.AArch64.WordState`, which this module and modules that import it used -/

section

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

end

end

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  baseReg : s.gpr .x0 = base
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .x2 = s.gpr .x2)
    (hkey : t.gpr .x0 = s.gpr .x0) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, hkey.trans hs.baseReg, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

theorem passPointer (base : Addr) (c : Nat) (d : Direction) :
    base + BitVec.ofNat 64 (passOffset c d) = keyAddr (componentBase base c) d 0 := by
  cases d
  · change base + BitVec.ofNat 64 (128 * c + 0) = base + BitVec.ofNat 64 (128 * c) + (0 : BitVec 64)
    exact (congrArg (fun n => base + BitVec.ofNat 64 n) (Nat.add_zero (128 * c))).trans
      (BitVec.add_zero (base + BitVec.ofNat 64 (128 * c))).symm
  · simp only [passOffset, keyAddr, componentBase, reduceCtorEq, ite_false]
    rw [Offset.add_ofNat_add_ofNat]


structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) (hs.regs .x2 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (hready : Ready keys base s) (hword : WordState x s)
    (hpasses : passesOf s = BitVec.ofNat 64 p) :
    WP isa (pass d) s (fun t =>
      WordState (VG.Proof.TripleDes.desCore (keys (passOf d p).1) (passOf d p).2 x) t ∧
      Ready keys base t ∧ Stable s t ∧
      passesOf t = BitVec.ofNat 64 (p - 1) ∧
      isa.eval (.nonzero .x .x3) t = some (decide (p ≠ 1))) := by
  have hc := passOf_lt d p
  have hptr : s.gpr .x0 + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr (componentBase base (passOf d p).1) (passOf d p).2 0 := by
    rw [hready.baseReg]
    exact passPointer base _ _
  apply WP.mono (pass_ok d hp (keys (passOf d p).1) (componentBase base (passOf d p).1) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hpasses hptr (hready.read _ hc _) (hready.separate _ hc _) (hready.values _ hc _))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .x2 (by decide)) (ht.regs .x0 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩, ht.passes, ht.zf⟩

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Save`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

def savedReg (i : Nat) : Reg := savedRegs.getD i .x19

theorem blockSave_eq : blockSave = Spill.saveCode .x2 (Spill.slots savedReg 4) := by
  decide +kernel

theorem blockRestore_eq : blockRestore = Spill.restoreCode .x2 (Spill.slots savedReg 4) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (current.gpr .x2 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  sp : current.sp = original.sp
  saved : Saved original current
  frame : Frame [⟨original.gpr .x2, 32⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq]
  refine WP.mono (Spill.save_wp (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, h.sp, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 4) (by decide) s.mem (s.gpr .x2) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.AArch64.Keep savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq]
  have hregs : (Spill.slots savedReg 4).map Prod.fst = savedRegs := by decide +kernel
  exact WP.mono (Spill.restore_wp rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.mem, h.rd, h.wr⟩,
      h.sp⟩

theorem savedSlot_spill_disjoint (s : State) (i : Nat) (hi : i < 4) :
    (⟨s.gpr .x2 + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .x2) (by omega_using [hi]) (by omega_using [hi]) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .x2 = s.gpr .x2) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .x2 + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .x2 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_spill_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.BlockIO`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Word`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

theorem mask_word (x : BitVec 64) (n : Nat) (hn : 0 < n) (hn64 : n ≤ 64) :
    (x <<< (64 - n)) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < n
  · have hi : 64 - n + j < 64 := by omega
    have hlo : ¬64 - n + j < 64 - n := by omega_using []
    simp only [hi, hlo, h, hj, decide_true, decide_false, Bool.not_false,
      Bool.true_and, show 64 - n + j - (64 - n) = j by omega_using []]
  · have ho : ¬64 - n + j < 64 := by omega_using [h]
    simp only [ho, h, hj, decide_true, decide_false, Bool.false_and, Bool.true_and]

theorem packHalves_shift (l r : BitVec 32) :
    l.setWidth 64 <<< 32 ^^^ r.setWidth 64 = l ++ r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : j < 32
  · simp [h, hj]
  · have hb : j - 32 < 32 := by omega_using [hj]
    simp [h, hj, hb, show j - 32 < 64 by omega_using [hj],
      BitVec.getLsbD_of_ge r j (by omega_using [h])]

theorem pack28_shift (c d : BitVec 28) :
    ((c.setWidth 64 <<< 28) ^^^ d.setWidth 64).setWidth 56 = c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  by_cases h : j < 28
  · simp [h, show j < 64 by omega_using [hj]]
  · simp [h, show j < 64 by omega_using [hj], show j - 28 < 28 by omega_using [hj],
      show j - 28 < 64 by omega_using [hj], BitVec.getLsbD_of_ge d j (by omega_using [h])]


end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Initial`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64
open VG VG.AArch64 VG.Impl.TripleDes.AArch64

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .x10 = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .x3).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds .x3 .x10 (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.AArch64
namespace VG.Proof.TripleDes.AArch64
open VG VG.AArch64 VG.Impl.TripleDes.AArch64

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12) s = some s' ∧
      s'.gpr .x10 = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x3) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12 =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, sp, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.AArch64

namespace VG.Proof.TripleDes.AArch64
open VG VG.AArch64 VG.Impl.TripleDes.AArch64
theorem final_ok (s : State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .x10 = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .x3).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds .x3 .x10 (instrs finalPermutation.lit) finalPermutation_check s

theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12) s = some s' ∧
      s'.gpr .x10 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .x3) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ := final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12 =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, sp, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.AArch64

end

end

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def loadKept : List Reg := [.x0, .x1, .x2, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8) :
    ∃ s', runBlock isa [.ldr .x .x3 .x1 0, .rev .x3 .x3] s = some s' ∧
      s'.gpr .x3 = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  have hload := exec_ldr_x (t := .x3) (n := .x1) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hread)
  refine ⟨_, by
    simp only [runBlock_cons, hload, runStep_some, runBlock_nil, exec_rev, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
    exact (decodeBlock_readW s.mem (s.gpr .x1)).symm
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

def splitHalves : List Instr :=
  [.lsr .x .x19 .x10 32, rr .x20 .x10] ++ mask .x20 32

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa splitHalves s = some s' ∧
      s'.gpr .x19 = s.gpr .x10 >>> 32 ∧
      s'.gpr .x20 = ((s.gpr .x10).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [splitHalves, mask, rr, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, Size.bits,
      show (32 : Nat) < 64 from by decide, show (0 : Nat) < 4096 from by decide,
      ite_true, State.read, gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact mask_word _ 32 (by decide) (by decide)
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r h19 h20; simp only [gpr_write, h19, h20, ite_false]

theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [h])
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy


theorem initial_preserves : loadKept.all (fun r =>
    (instrs initialPermutation.lit).all (fun op => !clobbers op r)) = true := by
  decide +kernel

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .x19 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .x20 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, sp₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .x10 = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1))) :=
    word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockLoad =
      (([.ldr .x .x3 .x1 0, .rev .x3 .x3] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12) ++ splitHalves := by
    simp only [blockLoad, splitHalves, List.append_assoc]
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hno := List.all_eq_true.mp initial_preserves r hr
    have hne : r ≠ .x3 ∧ r ≠ .x19 ∧ r ≠ .x20 := by revert hr; cases r <;> decide
    exact (regs₃ r hne.2.1 hne.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1))

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Block`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Head`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨s.gpr .x2, 32⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  pointer : s.gpr .x0 = base
  saveRead : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8
  dataSeparate : (⟨s.gpr .x1, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .x1)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  have hbase : t.gpr .x2 = s.gpr .x2 := congrFun hg .x2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, (congrFun hg .x0).trans hp.pointer, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : HeadPre keys base s) :
    WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (blockSave_ok s hp.saveWrite)
  intro s₁ hs₁
  have hready := ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1) 8 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (s₁.gpr .x1) =
      Spec.TripleDes.blockAt s.mem (s.gpr .x1) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ := blockLoad_ok s₁ hread₁
  have hframe : Frame [spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .x2 (by decide)) (regs₂ .x0 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .x2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

/-- The word after the first `k` passes of the block. -/
def passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    Nat → BitVec 64
  | 0 => x
  | k + 1 => desCore (keys (passOf direction (3 - k)).1) (passOf direction (3 - k)).2
      (passesDone keys direction x k)

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockCore_passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    blockCore keys direction x = passesDone keys direction x 3 := by
  cases direction <;> rfl

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : passesOf s = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₀ := s.write .x .x3 ((BitVec.ofNat 16 3).setWidth 64)
  let s₁ := s₀.setV .v1 (ofVDwords (s₀.gpr .x3) (s₀.gpr .x3))
  have hbase : s₁.gpr .x2 = s.gpr .x2 := by
    simp only [s₁, s₀, gpr_setV, gpr_write, reduceCtorEq, ite_false]
  have hrd : s₁.rd = s.rd := by simp only [s₁, s₀, rd_setV, rd_write]
  have hwr : s₁.wr = s.wr := by simp only [s₁, s₀, wr_setV, wr_write]
  have hsp : s₁.sp = s.sp := by simp only [s₁, s₀, sp_setV, sp_write]
  have hmem : s₁.mem = s.mem := by simp only [s₁, s₀, mem_setV, mem_write]
  have hframe : Frame [spillRegion s] s.mem s₁.mem := by rw [hmem]; exact Frame.refl _ _
  have hregs : ∀ r, r ≠ .x3 → s₁.gpr r = s.gpr r := by
    intro r hr
    simp only [s₁, s₀, gpr_setV, gpr_write, hr, ite_false]
  have hstable : Stable s s₁ := ⟨hrd, hwr, hsp,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, imm, show exec (.movz .x .x3 (BitVec.ofNat 16 3) 0) s = some s₀ from rfl,
      runStep_some, runBlock_cons, show exec (.vop (.dup .d2 .v1 .x3)) s₀ = some s₁ from rfl,
      runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, ?_, ?_, hready.congr hbase (hregs .x0 (by decide)) hrd hwr hframe,
      hstable⟩
  · rintro m t ⟨hpos, hle, hpasses, hw, hr, hst⟩
    refine WP.mono (pass_word_ok keys base t _ direction ⟨hpos, hle⟩ hr hw hpasses)
      fun u ⟨hwu, hru, hsu, hpu, hzu⟩ => ?_
    have hdone : desCore (keys (passOf direction m).1) (passOf direction m).2
        (passesDone keys direction x (3 - m)) = passesDone keys direction x (3 - (m - 1)) := by
      rw [show 3 - (m - 1) = 3 - m + 1 by omega_using [hpos, hle], passesDone, show 3 - (3 - m) = m by omega_using [hle]]
    rw [hdone] at hwu
    by_cases hlast : m = 1
    · subst m
      refine Or.inl ⟨by rw [hzu]; rfl, ?_, hru, hst.trans hsu⟩
      rw [blockCore_passesDone]
      exact hwu
    · refine Or.inr ⟨by rw [hzu]; simp [hlast], m - 1, by omega_using [hpos],
        ⟨by omega_using [hpos, hlast], by omega_using [hle], hpu, hwu, hru, hst.trans hsu⟩⟩
  · rw [passesOf, v_setV_self, VG.AArch64.vdword_ofVDwords_0]
    rfl
  · exact ⟨(hregs .x19 (by decide)).trans hword.left, (hregs .x20 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Tail`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def packHalves : List Instr := [.lsl .x .x3 .x19 32, .logic .eor .x .x3 .x3 .x20]

theorem packHalves_ok (s : State) :
    ∃ s', runBlock isa packHalves s = some s' ∧
      s'.gpr .x3 = s.gpr .x19 <<< 32 ^^^ s.gpr .x20 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [packHalves, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (32 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem storeTail_ok (s : State) :
    ∃ s', runBlock isa [.rev .x3 .x10] s = some s' ∧
      s'.gpr .x3 = rev64 (s.gpr .x10) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_rev]; rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, State.read, BitVec.setWidth_eq]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem final_preserves : loadKept.all (fun r =>
    (instrs finalPermutation.lit).all (fun op => !clobbers op r)) = true := by
  decide +kernel

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ loadKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ := packHalves_ok s
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := final_raw_ok s₁
  obtain ⟨s₃, run₃, word₃, mem₃, rd₃, wr₃, sp₃, regs₃⟩ := storeTail_ok s₂
  have hword : s₁.gpr .x3 = l ++ r := by
    rw [hl, hr] at word₁
    exact word₁.trans (packHalves_shift l r)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockStore =
      (packHalves ++ permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12) ++
      [.rev .x3 .x10] := rfl
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · exact word₃.trans (congrArg rev64 (word₂.trans
      (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) hword)))
  · intro q hq
    have hno := List.all_eq_true.mp final_preserves q hq
    have hneq : q ≠ .x3 := by revert hq; cases q <;> decide
    exact (regs₃ q hneq).trans ((regs₂ q hno).trans (regs₁ q hneq))

theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    ∃ s', runBlock isa [.str .x .x3 .x1 0] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x1) (s.gpr .x3) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hstore := exec_str_x (t := .x3) (n := .x1) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hwrite)
  refine ⟨{s with mem := s.mem.writeW (s.gpr .x1) (s.gpr .x3)}, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [runBlock_cons, hstore, runStep_some, runBlock_nil, BitVec.add_zero]

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .x1) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .x1, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (.block (blockStore ++ blockRestore ++ ([.str .x .x3 .x1 0] : List Instr)))
      s (TailPost original s x) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right
  have word : s₁.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    word₁.trans (congrArg (fun v => rev64 (Spec.TripleDes.permute Spec.TripleDes.fp v))
      (VG.Proof.TripleDes.halves_append x))
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .x2 (by decide), mem₁]
    exact hsaved i hi
  have savedRead₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .x2 (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hnonsaved : ∀ q ∈ (.x3 :: roundStepKept), q ∉ savedRegs := by decide
  have hrax₂ : s₂.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    (hs₂.keep.reg .x3 (hnonsaved .x3 (by decide))).trans word
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ (.x3 :: roundStepKept) ∧
      r ∈ loadKept := by decide
    exact (hs₂.keep.reg q (hnonsaved q (hkeep q hq).1)).trans (regs₁ q (hkeep q hq).2)
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .x1) 8 := by
    rw [hs₂.keep.wr, wr₁, hregs₂ .x1 (by decide)]
    exact hwrite
  obtain ⟨s₃, run₃, mem₃, gpr₃, rd₃, wr₃, sp₃⟩ := writeData_ok s₂ hwrite₂
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, ?_, rd₃.trans (hs₂.keep.rd.trans rd₁),
    wr₃.trans (hs₂.keep.wr.trans wr₁), sp₃.trans (hs₂.sp.trans sp₁), ?_, ?_⟩
  · rw [mem₃, hs₂.keep.mem, mem₁, hregs₂ .x1 (by decide), hrax₂]
    exact blockAt_writeW s.mem (s.gpr .x1) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · intro r hr
    rw [gpr₃]
    exact hs₂.saved r hr
  · intro q hq
    rw [gpr₃]
    exact hregs₂ q hq
  · rw [mem₃, hs₂.keep.mem, mem₁, hregs₂ .x1 (by decide)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (original.gpr .x1) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (original.gpr .x1))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : Addr) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ loadKept := by decide
    exact (hs₂.2.2.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.regs .x2 (by decide)) hs₂.2.2.frame
  have savedRead₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [hs₂.2.2.rd, hs₂.2.2.wr, hs₁.rd, hs₁.wr, hregs₂ .x2 (by decide)]
    exact hp.saveRead
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .x1) 8 := by
    rw [hs₂.2.2.wr, hs₁.wr, hregs₂ .x1 (by decide)]
    exact hwrite
  apply WP.mono (blockTail_ok s s₂ _ hs₂.1 saved₂ savedRead₂ hwrite₂)
  intro s₃ hs₃
  refine ⟨?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.wr.trans hs₁.wr),
    hs₃.sp.trans (hs₂.2.2.sp.trans hs₁.sp),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .x1 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨s.gpr .x2, 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨s.gpr .x2, 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .x2 (by decide)
      change Region.Sub ⟨s₁.gpr .x2 + BitVec.ofNat 64 32, 384⟩ ⟨s.gpr .x2, 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .x1 (by decide)]
      exact ⟨⟨s.gpr .x1, 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let data : Region := ⟨s.gpr .x1, 8⟩
    let scratch : Region := ⟨s.gpr .x2, 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .x1) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (Spec.TripleDes.blockAt s.mem (s.gpr .x1))
  pub := PublicRegs [.x0, .x1, .x2]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])

/-- The block function's precondition, from its 512 bytes of scratch at
`x2` writable, the schedule at `x0` readable and the block at `x1`
writable, neither in the scratch. -/
theorem headPre_of (s : State)
    (scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (keyReads : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8)
    (dataWrite : InRegions s.wr (s.gpr .x1) 8)
    (keySep : Region.Disjoint ⟨s.gpr .x0, 384⟩ ⟨s.gpr .x2, 512⟩)
    (dataSep : Region.Disjoint ⟨s.gpr .x1, 8⟩ ⟨s.gpr .x2, 512⟩) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
      (s.gpr .x0) s := by
  have inRd : ∀ {a n}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, h1, h2⟩ =>
    ⟨r, List.mem_append_right _ h1, h2⟩
  have spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .x0) c) direction j, 8⟩ ⟨s.gpr .x0, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, hindex])
  have workSub : Region.Sub (spillRegion s) ⟨s.gpr .x2, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .x2, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨spills, rfl, (fun i hi => inRd (scratchWrites i (by omega_using [hi]))),
    (fun i hi => scratchWrites i (by omega_using [hi])), inRd dataWrite, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact keyReads _ (by have := selectedRound_bound direction j hj; omega_using [hc, this])
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .x0) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
      (s.gpr .x0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  refine headPre_of s (fun i hi => ?_) (fun i hi => ?_) ?_ keySep dataSep
  · rw [hwr]
    exact ⟨⟨s.gpr .x2, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .x0, 384⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hwr]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩


end VG.Proof.TripleDes.AArch64

end

end

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => GprAbi s s' ∧ (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .x1) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x0) d s hp hwrite)
  intro s' hpost
  refine ⟨⟨?_, hpost.sp⟩, hpost.result⟩
  intro r hr
  have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ roundStepKept := by decide
  rcases hkeep r hr with h | h
  · exact hpost.saved r h
  · exact hpost.regs r h

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

end VG.Proof.TripleDes.AArch64
