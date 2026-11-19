module

public import VerifiedGarbage.Impl.Argon2.AArch64.DependentWord
public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.FillStep
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressLit
public import VerifiedGarbage.Impl.Argon2.AArch64.FillKernel
import VerifiedGarbage.Proof.Argon2.AArch64.Carry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Impl.Argon2.AArch64.Wrap
import VerifiedGarbage.Proof.Argon2.Reference
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Argon2.AArch64.Wrap
meta import VerifiedGarbage.Proof.Argon2.Reference
meta import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
meta import VerifiedGarbage.Proof.Argon2.AArch64.Carry
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Argon2.AArch64.Relative
import VerifiedGarbage.Proof.Argon2.AArch64.Mix
meta import VerifiedGarbage.Impl.Argon2.AArch64.Relative
meta import VerifiedGarbage.Proof.Argon2.AArch64.Mix
public import VerifiedGarbage.Proof.Argon2.AArch64.Remainder
meta import VerifiedGarbage.Proof.Argon2.AArch64.Divide
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount
public import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceMap
meta import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount
meta import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceMap
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceStart
public import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates

/-! ### `Argon2.AArch64.FillKernelArgs`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.ReferenceMap`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.ReferenceStart`, which this module and modules that import it used -/

section

/-! The reference window starts at the next slice on later passes. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.ReferenceStart

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceStart
open VG.Impl.Argon2.AArch64

theorem sub_zero_iff (x y : Addr) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = (x - y) + y := (BitVec.sub_add_cancel x y).symm
      _ = y := by rw [h]; exact BitVec.zero_add y
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem zero_ok (s : State) : WP isa (.block zero) s fun t =>
    t.gpr .x6 = 0 ∧ Divide.Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [zero, Instructions.imm, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true,
    BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .x6 = (s.gpr .x22 + 1) * s.gpr .x21 ∧
    t.gpr .x15 = s.gpr .x22 - 3 ∧ Divide.Keeps [.x8, .x2, .x6, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [advance, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.addi, Instructions.mul, Instructions.mark,
    Instructions.comparei, Instructions.compare, Instructions.imm,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true,
    show 1 < 4096 from by decide, show 0 < 4096 from by decide,
    show 3 < 65536 from by decide,
    show (BitVec.ofNat 16 3).setWidth 64 = 3#64 from rfl,
    show (3#64) = (3 : Addr) from rfl,
    show (BitVec.ofNat 64 1) = (1 : Addr) from rfl]
  refine ⟨trivial, sub_value _ _, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x8, .x2, .x6, .x13, .x14, .x15]

def value (s : State) : Addr :=
  if s.gpr .x5 = 0 then 0 else
    if s.gpr .x22 = 3 then 0 else (s.gpr .x22 + 1) * s.gpr .x21

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x6 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
  · intro h
    have firstPass : s.gpr .x5 = 0 := of_decide_eq_true h
    refine (zero_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [value, firstPass, ite_true] using out
  · intro h
    have laterPass : s.gpr .x5 ≠ 0 := of_decide_eq_false h
    refine WP.seq ((advance_ok a).mono ?_)
    rintro b ⟨out, flag, advanceKeeps⟩
    have sliceReg := keeps.regs .x22 (by simp)
    have segmentReg := keeps.regs .x21 (by simp)
    refine WP.ite (decide (s.gpr .x22 = 3))
      (by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, sliceReg]
        apply congrArg some
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, decide_eq_true_eq]
        exact sub_zero_iff _ _) ?_ ?_
    · intro h
      have lastSlice : s.gpr .x22 = 3 := of_decide_eq_true h
      refine (zero_ok b).mono ?_
      rintro t ⟨out, tail⟩
      refine ⟨?_, ((keeps.mono (by decide)).trans advanceKeeps).trans (tail.mono (by decide))⟩
      simpa only [value, laterPass, lastSlice, ite_false, ite_true] using out
    · intro h
      have earlierSlice : s.gpr .x22 ≠ 3 := of_decide_eq_false h
      apply WP.of_runBlock
      simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
      refine ⟨?_, (keeps.mono (by decide)).trans advanceKeeps⟩
      simpa only [value, laterPass, earlierSlice, ite_false, sliceReg, segmentReg] using out

theorem start_nat (p : Spec.Argon2.Params) (hl : 0 < p.lanes)
    (hg : 0 < p.segmentLen) (slice : Nat) (hs : slice < 4) :
    (slice + 1) * p.segmentLen % p.laneLen =
      if slice = 3 then 0 else (slice + 1) * p.segmentLen := by
  rw [Proof.Argon2.laneLen_segments p hl]
  by_cases lastSlice : slice = 3
  · simp only [lastSlice, ite_true, show (3 : Nat) + 1 = 4 from rfl, Nat.mod_self]
  · have smaller : (slice + 1) * p.segmentLen < 4 * p.segmentLen :=
      Nat.mul_lt_mul_of_pos_right (by omega_using [hs, lastSlice]) hg
    rw [Nat.mod_eq_of_lt smaller]
    simp only [lastSlice, ite_false]

theorem value_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .x5).toNat = pass)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen) :
    value s = BitVec.ofNat 64
      (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) := by
  have isZero : s.gpr .x5 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  have isLast : s.gpr .x22 = 3 ↔ slice = 3 := by
    rw [sliceReg]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hs])] at hn
      exact hn
    · intro h; rw [h]; rfl
  unfold value
  simp only [isZero, isLast]
  by_cases firstPass : pass = 0
  · simp only [firstPass, ite_true]; rfl
  · simp only [firstPass, ite_false, start_nat p hl hg slice hs]
    by_cases lastSlice : slice = 3
    · simp only [lastSlice, ite_true]; rfl
    · simp only [lastSlice, ite_false]
      rw [sliceReg, segmentReg]
      change (BitVec.ofNat 64 slice + BitVec.ofNat 64 1) *
        BitVec.ofNat 64 p.segmentLen = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .x5).toNat = pass)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen) :
    WP isa code s fun t =>
      t.gpr .x6 = BitVec.ofNat 64
        (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) ∧
      Divide.Keeps changed s t :=
  (code_ok s).mono (fun _ h =>
    ⟨h.1.trans (value_nat s p pass slice hl hg hs passReg sliceReg segmentReg), h.2⟩)

end VG.Proof.Argon2.AArch64.ReferenceStart

end

end

/-! ### `Argon2.AArch64.ReferenceMapLane`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.ReferenceMapState`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapArgs`. -/

@[expose] public section

section
/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap
open VG.Impl.Argon2.AArch64

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .x19) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .x5 = s.mem.readW (s.gpr .x19) 64 ∧ Divide.Keeps [.x5] s t := by
  apply WP.of_runBlock
  simp only [loadPass, Instructions.load, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, Size.bits, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide,
    BitVec.add_zero, State.load, read, and_self, ite_true, Option.map_some, Option.bind_some,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .x0 = s.gpr .x4 ∧ t.gpr .x1 = s.gpr .x24 ∧
    Divide.Keeps [.x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .x5 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x7 ∧ t.gpr .x1 = s.gpr .x4 ∧
    Divide.Keeps [.x5, .x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .x0 = s.gpr .x8 + s.gpr .x6 ∧ t.gpr .x1 = s.gpr .x20 ∧
    Divide.Keeps [.x0, .x1, .x15] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, Instructions.mov, Instructions.add, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Parameters and register invariants for the complete reference mapping. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64

/-- Every stage preserves the enclosing loop's callee-saved registers. -/
def changed : List Reg := [.x8, .x2, .x3, .x4, .x5, .x6, .x7, .x0, .x1, .x9, .x12, .x13, .x14, .x15]

structure Bounds (p : Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4
  indexBound : index < p.segmentLen
  active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index

structure Position (p : Spec.Argon2.Params) (lane slice index : Nat) (s : State) : Prop where
  current : s.gpr .x24 = BitVec.ofNat 64 lane
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  slice : s.gpr .x22 = BitVec.ofNat 64 slice
  index : s.gpr .x23 = BitVec.ofNat 64 index

theorem Position.of_keeps {s t : State} {p : Spec.Argon2.Params} {lane slice index : Nat}
    (h : Position p lane slice index s) (k : Divide.Keeps changed s t) :
    Position p lane slice index t :=
  ⟨(k.regs .x24 (by decide)).trans h.current,
    (k.regs .x20 (by decide)).trans h.laneLength,
    (k.regs .x21 (by decide)).trans h.segmentLength,
    (k.regs .x22 (by decide)).trans h.slice,
    (k.regs .x23 (by decide)).trans h.index⟩

structure Ready (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s : State) : Prop where
  bounds : Bounds p pass lane slice index
  position : Position p lane slice index s
  lanes : s.gpr .x1 = BitVec.ofNat 64 p.lanes
  passRead : InRegions (s.rd ++ s.wr) (s.gpr .x19) 8
  passWord : s.mem.readW (s.gpr .x19) 64 = BitVec.ofNat 64 pass

theorem Ready.lanes_nat {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s : State}
    (h : Ready p pass lane slice index s) : (s.gpr .x1).toNat = p.lanes := by
  rw [h.lanes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bounds.lanesBound (by decide))]

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : Ready p pass lane slice index s) (k : Divide.Keeps changed s t)
    (lanes : t.gpr .x1 = s.gpr .x1) : Ready p pass lane slice index t := by
  refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanes, ?_, ?_⟩
  · rw [k.rd, k.wr, k.regs .x19 (by decide)]
    exact h.passRead
  · rw [k.mem, k.regs .x19 (by decide)]
    exact h.passWord

def chosenLane (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr) : Nat :=
  if pass = 0 ∧ slice = 0 then lane else (random >>> 32).toNat % p.lanes

theorem chosenLane_bound (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr)
    (positive : 0 < p.lanes) (bound : lane < p.lanes) :
    chosenLane p pass lane slice random < p.lanes := by
  unfold chosenLane
  split
  · exact bound
  · exact Nat.mod_lt _ positive

theorem word_nat (n : Nat) (bound : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem word_zero (n : Nat) (bound : n < 2 ^ 64) : BitVec.ofNat 64 n = (0 : Addr) ↔ n = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [word_nat n bound] at hn
    exact hn
  · intro h; rw [h]; rfl

theorem word_eq (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [word_nat x hx, word_nat y hy] at hn
    exact hn
  · intro h; rw [h]

theorem Bounds.laneLength_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : p.laneLen < 2 ^ 32 := by
  have hb : p.laneLen ≤ p.blocks := by
    rw [Proof.Argon2.blocks_lanes p h.lanesPositive]
    exact Nat.le_mul_of_pos_left _ h.lanesPositive
  exact Nat.lt_of_le_of_lt (Nat.le_trans hb (Proof.Argon2.blocks_le_memory p)) h.memoryBound

theorem Bounds.window_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) :
    0 < ReferenceCount.windowBase p pass slice + index ∧
      (index = 0 → 0 < ReferenceCount.windowBase p pass slice) := by
  have hp := Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index true h.active (by intro _ _; rfl)
  rw [ReferenceCount.spec_count] at hp
  change 0 < ReferenceCount.windowBase p pass slice + index - 1 at hp
  constructor
  · omega_using [hp]
  · intro zero; rw [zero, Nat.add_zero] at hp; omega_using [hp]

def windowSize (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  Spec.Argon2.referenceCount p pass slice index (chosenLane p pass lane slice random == lane)

def windowStart (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen

def relativeValue (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  let count := windowSize p pass lane slice index random
  let j := (random &&& 0xffffffff).toNat
  count - 1 - count * (j * j / 2 ^ 32) / 2 ^ 32

theorem Bounds.segment_le_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : p.segmentLen ≤ p.laneLen := by
  have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega_using [segments]

theorem Bounds.index_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : index < 2 ^ 64 :=
  Nat.lt_trans (Nat.lt_of_lt_of_le h.indexBound h.segment_le_lane)
    (Nat.lt_trans h.laneLength_bound (by decide))

theorem Bounds.chosenLane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    chosenLane p pass lane slice random < 2 ^ 64 :=
  Nat.lt_trans (chosenLane_bound p pass lane slice random h.lanesPositive h.laneBound)
    (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.lane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : lane < 2 ^ 64 :=
  Nat.lt_trans h.laneBound (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.windowSize_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    0 < windowSize p pass lane slice index random := by
  apply Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index _ h.active
  intro firstPass firstSlice
  simp only [chosenLane, firstPass, firstSlice, and_self, ite_true]
  exact beq_iff_eq.mpr rfl

theorem Bounds.windowSize_bound32 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    windowSize p pass lane slice index random < 2 ^ 32 :=
  Proof.Argon2.reference_count_32 p h.lanesPositive h.memoryMinimum h.memoryBound
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.windowSize_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    windowSize p pass lane slice index random < p.laneLen :=
  Proof.Argon2.reference_count_lt_lane p h.lanesPositive h.memoryMinimum
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.laneLength_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : 0 < p.laneLen := by
  have seg := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have len := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega_using [seg, len]

theorem Bounds.windowStart_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : windowStart p pass slice < p.laneLen := by
  unfold windowStart
  split
  · exact h.laneLength_positive
  · exact Nat.mod_lt _ h.laneLength_positive

theorem Bounds.sum_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    windowStart p pass slice + relativeValue p pass lane slice index random < 2 * p.laneLen := by
  have start := h.windowStart_lt_lane
  have relative := Proof.Argon2.reference_relative_bound _ (random &&& 0xffffffff).toNat
    (h.windowSize_positive random)
  have count := h.windowSize_lt_lane random
  change relativeValue p pass lane slice index random < windowSize p pass lane slice index random at relative
  omega_using [start, count, relative]

end VG.Proof.Argon2.AArch64.ReferenceMap

end

end

/-! Merged from `Proof.Argon2.AArch64.ReferenceLane`. -/

@[expose] public section

section
/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.AArch64.ReferenceLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceLane
open VG.Impl.Argon2.AArch64

structure Prefix (s t : State) : Prop where
  high : t.gpr .x0 = s.gpr .x0 >>> 32
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps [.x0, .x7, .x15] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, Instructions.mov, Instructions.shr, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 32 < 64 from by decide, show 0 < 4096 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x0, .x7, .x15, .x3, .x4, .x6, .x8, .x5, .x9]

theorem code_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x0 >>> 32).toNat % (s.gpr .x1).toNat ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .x1 (by decide)
  refine (Remainder.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .x0) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.mono (by decide))⟩
    · rw [ht.1, ha.high, si]
    · exact (ht.2.regs .x7 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr

theorem highArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block highArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  highArgs_secret_rel.seq Remainder.code_secret_rel

end VG.Proof.Argon2.AArch64.ReferenceLane
end

/-! Merged from `Proof.Argon2.AArch64.FirstLane`. -/
section
/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.AArch64.FirstLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FirstLane
open VG.Impl.Argon2.AArch64

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.gpr .x15 = s.gpr .x5 ||| s.gpr .x22 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [test, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.logic, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .x4 = s.gpr .x24 ∧ Divide.Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [current, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, ite_true, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x4 = (if s.gpr .x5 = 0 ∧ s.gpr .x22 = 0 then s.gpr .x24 else s.gpr .x4) ∧
    Divide.Keeps [.x8, .x4, .x15] s t := by
  unfold code
  refine WP.seq ((test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0 ∧ s.gpr .x22 = 0))
    (by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact BitVec.or_eq_zero_iff) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .x24 (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .x4 (by decide)

end VG.Proof.Argon2.AArch64.FirstLane
end

/-! Choose the reference lane, restore the pass and prepare the window inputs. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Chosen (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x4 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  pass : t.gpr .x5 = BitVec.ofNat 64 pass
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem chooseLane_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa chooseLane s (Chosen p pass lane slice index s) := by
  have lanesNat : (s.gpr .x1).toNat = p.lanes := by
    rw [ready.lanes, word_nat _ (by have := ready.bounds.lanesBound; omega_using [this])]
  unfold chooseLane
  refine WP.seq ((ReferenceLane.code_ok s
    (by rw [lanesNat]; exact ready.bounds.lanesPositive)
    (by rw [lanesNat]; exact ready.bounds.lanesBound)).mono ?_)
  rintro a ⟨laneNat, original, ka⟩
  have ka' : Divide.Keeps changed s a := ka.mono (by decide)
  have readA : InRegions (a.rd ++ a.wr) (a.gpr .x19) 8 := by
    rw [ka'.rd, ka'.wr, ka'.regs .x19 (by decide)]
    exact ready.passRead
  have laneWord : a.gpr .x4 = BitVec.ofNat 64 ((s.gpr .x0 >>> 32).toNat % p.lanes) := by
    calc
      a.gpr .x4 = BitVec.ofNat 64 (a.gpr .x4).toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [laneNat, lanesNat]
  refine WP.seq ((loadPass_ok a readA).mono ?_)
  rintro b ⟨loaded, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kab := ka'.trans kb'
  have pb := ready.position.of_keeps kab
  have passWord : b.gpr .x5 = BitVec.ofNat 64 pass := by
    rw [loaded, ka'.mem, ka'.regs .x19 (by decide)]
    exact ready.passWord
  have passZero : b.gpr .x5 = 0 ↔ pass = 0 := by
    rw [passWord]
    exact word_zero _ (by have := ready.bounds.passBound; omega_using [this])
  have sliceZero : b.gpr .x22 = 0 ↔ slice = 0 := by
    rw [pb.slice]
    exact word_zero _ (by have := ready.bounds.sliceBound; omega_using [this])
  refine (FirstLane.code_ok b).mono ?_
  rintro t ⟨out, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ready.position.of_keeps (kab.trans kt'), kab.trans kt'⟩
  · rw [out]
    by_cases position : pass = 0 ∧ slice = 0 <;>
      simp only [passZero, sliceZero, pb.current, kb.regs .x4 (by decide), laneWord,
        chosenLane, position, and_self, ite_true, ite_false]
  · exact (kt.regs .x5 (by decide)).trans passWord
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans original)

structure Prepared (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x0 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  current : t.gpr .x1 = BitVec.ofNat 64 lane
  pass : (t.gpr .x5).toNat = pass
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem prepareLanes_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa prepareLanes s (Prepared p pass lane slice index s) := by
  unfold prepareLanes
  refine WP.seq ((chooseLane_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine (laneArgs_ok a).mono ?_
  rintro t ⟨laneOut, currentOut, kt⟩
  have kt' : Divide.Keeps changed a t := kt.mono (by decide)
  refine ⟨laneOut.trans ha.selected, currentOut.trans ha.position.current, ?_,
    (kt.regs .x7 (by decide)).trans ha.original,
    ha.position.of_keeps kt', ha.keeps.trans kt'⟩
  rw [kt.regs .x5 (by decide), ha.pass, word_nat _ (by have := ready.bounds.passBound; omega_using [this])]

end VG.Proof.Argon2.AArch64.ReferenceMap

end

end

/-! ### `Argon2.AArch64.Relative`, which this module and modules that import it used -/

section

/-! # The baseline reference-window mapping is fixed time and preserves memory -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Relative

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Relative
open VG.Impl.Argon2.AArch64

def value (random count : Addr) : Addr :=
  let j := random &&& 0xffffffff
  let x := (j * j) >>> 32
  let y := (x * count) >>> 32
  count - 1 - y

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x8 = value (s.gpr .x0) (s.gpr .x1) ∧
    (∀ r, r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.mov32, Instructions.mul, Instructions.shr,
    Instructions.subi, Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry,
    BitVec.setWidth_eq, BitVec.or_self, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    show 32 < 64 from by decide, BitVec.add_zero, Option.some.injEq,
    exists_eq_left', Bool.toNat_true, sub_value]
  refine ⟨?_, ?_, trivial, trivial, trivial⟩
  · rw [low32]; rfl
  · intro r h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, ite_false]

theorem mul_shift_toNat (x y : Addr) (bound : x.toNat * y.toNat < 2 ^ 64) :
    ((x * y) >>> 32).toNat = x.toNat * y.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
    Nat.mod_eq_of_lt bound]

theorem value_nat (random count : Addr) (lo : 0 < count.toNat)
    (bound : count.toNat < 2 ^ 32) :
    value random count = BitVec.ofNat 64
      (count.toNat - 1 - count.toNat * ((random &&& 0xffffffff).toNat *
        (random &&& 0xffffffff).toNat / 2 ^ 32) / 2 ^ 32) := by
  let j := random &&& 0xffffffff
  have hj : j.toNat < 2 ^ 32 := by
    have h32 := (random.setWidth 32).isLt
    rw [show j = (random.setWidth 32).setWidth 64 from (low32 random).symm,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [])]
    exact h32
  have hx := mul_shift_toNat j j (Proof.Argon2.reference_square_bound _ hj)
  have product : ((j * j) >>> 32).toNat * count.toNat < 2 ^ 64 := by
    rw [hx, Nat.mul_comm]
    exact Proof.Argon2.reference_product_bound _ _ bound hj
  have hy := mul_shift_toNat ((j * j) >>> 32) count product
  rw [hx, Nat.mul_comm] at hy
  have hyBound : count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32 < count.toNat :=
    Proof.Argon2.reference_scale_lt_count _ _ lo hj
  have hyWord : (((j * j) >>> 32) * count) >>> 32 = BitVec.ofNat 64
      (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hy])]
  unfold value
  change count - 1 - ((((j * j) >>> 32) * count) >>> 32) = _
  rw [hyWord]
  change count - (1 : Addr) - BitVec.ofNat 64
    (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) = _
  have countWord : count = BitVec.ofNat 64 count.toNat := by
    exact (BitVec.ofNat_toNat 64 count).symm
  have countSub : count - 1 = BitVec.ofNat 64 (count.toNat - 1) := by
    calc
      count - 1 = BitVec.ofNat 64 count.toNat - BitVec.ofNat 64 1 :=
        congrArg (fun x : Addr => x - 1) countWord
      _ = _ := Offset.ofNat_sub_ofNat (by omega_using [lo])
  rw [countSub, Offset.ofNat_sub_ofNat (by omega_using [hyBound])]

theorem code_nat_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      t.gpr .x8 = BitVec.ofNat 64
        ((s.gpr .x1).toNat - 1 - (s.gpr .x1).toNat *
          ((s.gpr .x0 &&& 0xffffffff).toNat * (s.gpr .x0 &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧
      (∀ r, r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (value_nat _ _ lo bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Relative

end

end

/-! ### `Argon2.AArch64.Wrap`, which this module and modules that import it used -/

section

/-! # Masked subtraction agrees with wrapping the reference column -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Wrap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Wrap
open VG.Impl.Argon2.AArch64

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x0 = (if (s.gpr .x0).toNat < (s.gpr .x1).toNat
      then s.gpr .x0 else s.gpr .x0 - s.gpr .x1) ∧
    Divide.Keeps [.x0, .x6, .x8, .x15] s t := by
  unfold code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.sub, Instructions.sbb, Instructions.logic,
    Instructions.mark, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', Bool.toNat_true, sub_value, sub_carry,
    borrow_mask]
  have hm : (if decide ((s.gpr .x1).toNat ≤ (s.gpr .x0).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x0).toNat < (s.gpr .x1).toNat)) := by
    by_cases h : (s.gpr .x0).toNat < (s.gpr .x1).toNat <;>
      simp [Divide.mask, h, Nat.le_of_not_gt, Nat.not_le_of_gt]
  rw [hm, Divide.select_value]
  simp only [decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem wrap_nat (x q : Addr) (bound : x.toNat < 2 * q.toNat) :
    (if x.toNat < q.toNat then x else x - q) = BitVec.ofNat 64 (x.toNat % q.toNat) := by
  rw [Proof.Argon2.reference_wrap _ _ bound]
  by_cases small : x.toNat < q.toNat
  · rw [ite_eq_left small, ite_eq_left small]
    exact (BitVec.ofNat_toNat 64 x).symm
  · rw [ite_eq_right small, ite_eq_right small]
    calc
      x - q = BitVec.ofNat 64 x.toNat - BitVec.ofNat 64 q.toNat := by
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := Offset.ofNat_sub_ofNat (by omega_using [small])

theorem code_nat_ok (s : State) (bound : (s.gpr .x0).toNat < 2 * (s.gpr .x1).toNat) :
    WP isa code s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 ((s.gpr .x0).toNat % (s.gpr .x1).toNat) ∧
      Divide.Keeps [.x0, .x6, .x8, .x15] s t :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (wrap_nat _ _ bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Wrap

end

end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapWindow`. -/

@[expose] public section

section
/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x0 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  current : t.gpr .x1 = BitVec.ofNat 64 lane
  count : t.gpr .x4 = BitVec.ofNat 64 (windowSize p pass lane slice index (s.gpr .x0))
  start : t.gpr .x6 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem window_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (prepared : Prepared p pass lane slice index s a) :
    WP isa window a (Counted p pass lane slice index s) := by
  have segmentPositive : 0 < p.segmentLen :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2)
      (Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum)
  unfold window
  refine WP.seq ((ReferenceStart.code_nat_ok a p pass slice bounds.lanesPositive
    segmentPositive bounds.sliceBound prepared.pass prepared.position.slice
    prepared.position.segmentLength).mono ?_)
  rintro b ⟨startWord, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have pb := prepared.position.of_keeps kb'
  have passB : (b.gpr .x5).toNat = pass := by
    rw [kb.regs .x5 (by decide), prepared.pass]
  have same : decide (b.gpr .x0 = b.gpr .x1) =
      (chosenLane p pass lane slice (s.gpr .x0) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .x0 (by decide), kb.regs .x1 (by decide), prepared.selected, prepared.current]
    exact word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x0 (by decide)).trans ((kb.regs .x0 (by decide)).trans prepared.selected)
  · exact (kt.regs .x1 (by decide)).trans ((kb.regs .x1 (by decide)).trans prepared.current)
  · simpa only [windowSize, same] using countWord
  · exact (kt.regs .x6 (by decide)).trans startWord
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans prepared.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapRelative`. -/
section
/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.AArch64.Relative.code s fun t =>
      t.gpr .x8 = BitVec.ofNat 64
        ((s.gpr .x1).toNat - 1 - (s.gpr .x1).toNat *
          ((s.gpr .x0 &&& 0xffffffff).toNat * (s.gpr .x0 &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.x8, .x2, .x3, .x12, .x15] s t := by
  obtain ⟨tr, t, he, out, other, mem, rd, wr⟩ := Relative.code_nat_ok s positive bound
  refine ⟨tr, t, he, out, ?_⟩
  refine ⟨?_, mem, rd, wr, VG.AArch64.Exec.sp he⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  relative : t.gpr .x8 = BitVec.ofNat 64 (relativeValue p pass lane slice index (s.gpr .x0))
  start : t.gpr .x6 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (counted : Counted p pass lane slice index s a) :
    WP isa relative a (Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .x1).toNat = windowSize p pass lane slice index (s.gpr .x0) := by
    rw [count, counted.count, word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .x0 = s.gpr .x0 := random.trans counted.original
  refine (relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x5 (by decide)).trans (selected.trans counted.selected)
  · simpa only [relativeValue, countNat, randomWord] using out
  · exact (kt.regs .x6 (by decide)).trans ((kb.regs .x6 (by decide)).trans counted.start)
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans counted.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapFinish`. -/
section
/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  column : t.gpr .x0 = BitVec.ofNat 64
    ((windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0)) % p.laneLen)
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (mapped : Mapped p pass lane slice index s a) :
    WP isa finish a (Result p pass lane slice index s) := by
  unfold finish
  refine WP.seq ((wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .x0 = BitVec.ofNat 64
      (windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .x0)
    have q := bounds.laneLength_bound
    omega_using [small, q]
  have sumNat : (b.gpr .x0).toNat =
      windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0) := by
    rw [sumWord, word_nat _ sumBound]
  have lengthNat : (b.gpr .x1).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x5 (by decide)).trans ((kb.regs .x5 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans mapped.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem code_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s (Result p pass lane slice index s) := by
  unfold code
  refine WP.seq ((prepareLanes_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine WP.seq ((window_ok s a p pass lane slice index ready.bounds ha).mono ?_)
  intro b hb
  refine WP.seq ((relative_ok s b p pass lane slice index ready.bounds hb).mono ?_)
  intro c hc
  exact finish_ok s c p pass lane slice index ready.bounds hc

theorem spec_lane (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).1 = chosenLane p pass lane slice random := rfl

theorem spec_column (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).2 =
      (windowStart p pass slice + relativeValue p pass lane slice index random) % p.laneLen := rfl

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s fun t =>
      t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1 ∧
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2 ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps changed s t := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [spec_lane, spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.AArch64.ReferenceMap

end

end

/-! Merged from `Proof.Argon2.AArch64.FillPointersNat`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.FillPointersArgs`. -/
section
/-! Short register-setup steps for the filling pointers. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

theorem saveReference_ok (s : State) : WP isa (.block saveReference) s fun t =>
    t.gpr .x1 = s.gpr .x0 ∧ Divide.Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [saveReference, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact by simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem currentArgs_ok (s : State) : WP isa (.block currentArgs) s fun t =>
    t.gpr .x8 = s.gpr .x24 ∧ Divide.Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [currentArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact by simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem previousArgs_ok (s : State) : WP isa (.block previousArgs) s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧ t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x8 = s.gpr .x24 ∧
    Divide.Keeps [.x6, .x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [previousArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem referenceArgs_ok (s : State) : WP isa (.block referenceArgs) s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧ t.gpr .x3 = s.gpr .x1 ∧ t.gpr .x8 = s.gpr .x5 ∧
    Divide.Keeps [.x7, .x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [referenceArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finishArgs_ok (s : State) : WP isa (.block finishArgs) s fun t =>
    t.gpr .x1 = s.gpr .x8 ∧ t.gpr .x0 = s.gpr .x7 ∧
    Divide.Keeps [.x1, .x0] s t := by
  apply WP.of_runBlock
  simp only [finishArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillPointers`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillColumn`. -/
section
/-! Current-column arithmetic and the cyclic predecessor, preserving the
matrix, enclosing loop registers and the stack pointer. -/

namespace VG.Proof.Argon2.AArch64.FillColumn

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillColumn
open VG.Impl.Argon2.AArch64

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .x3 = s.gpr .x22 * s.gpr .x21 + s.gpr .x23 ∧
    Divide.Keeps [.x8, .x2, .x3, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [current, Instructions.mov, Instructions.mul, Instructions.add,
    Instructions.mark, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left' ]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [Instructions.comparei .x3 0].flatten) s
    fun t => t.gpr .x15 = s.gpr .x3 ∧ Divide.Keeps [.x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.comparei, Instructions.compare, Instructions.imm,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    reduceCtorEq, ite_true, ite_false, show 0 < 65536 from by decide,
    Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 0).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem move_ok (s : State) (r : Reg) : WP isa (.block [Instructions.mov .x0 r].flatten) s
    fun t => t.gpr .x0 = s.gpr r ∧ Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.mov, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left' ]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, ite_false]
  all_goals rfl

theorem decrement_ok (s : State) : WP isa (.block [Instructions.subi .x0 1].flatten) s
    fun t => t.gpr .x0 = s.gpr .x0 - 1 ∧ Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.subi, Instructions.sub, Instructions.imm, Instructions.mark, Instructions.mov,
    RegUpd.gpr_addWithCarry, show 1 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left' ]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .x0 = (if s.gpr .x3 = 0 then s.gpr .x20 else s.gpr .x3) - 1 ∧
    Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  unfold previous
  refine WP.seq ((compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have selected : WP isa select a fun b =>
      b.gpr .x0 = (if s.gpr .x3 = 0 then s.gpr .x20 else s.gpr .x3) ∧
      Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s b := by
    unfold select
    refine WP.ite (decide (s.gpr .x3 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
    · intro h
      have zero := of_decide_eq_true h
      refine (move_ok a .x20).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .x20 (by decide), ite_eq_left zero],
        (ka.mono (by decide)).trans kb⟩
    · intro h
      have nonzero := of_decide_eq_false h
      refine (move_ok a .x3).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .x3 (by decide), ite_eq_right nonzero],
        (ka.mono (by decide)).trans kb⟩
  refine WP.seq (selected.mono ?_)
  rintro b ⟨value, kb⟩
  refine (decrement_ok b).mono ?_
  rintro t ⟨result, kt⟩
  exact ⟨by rw [result, value], kb.trans kt⟩

theorem code_ok (s : State) : WP isa code s fun t =>
    let column := s.gpr .x22 * s.gpr .x21 + s.gpr .x23
    t.gpr .x3 = column ∧
    t.gpr .x0 = (if column = 0 then s.gpr .x20 else column) - 1 ∧
    Divide.Keeps [.x8, .x2, .x3, .x0, .x12, .x13, .x14, .x15] s t := by
  unfold code
  refine WP.seq ((current_ok s).mono ?_)
  rintro a ⟨column, ka⟩
  refine (previous_ok a).mono ?_
  rintro t ⟨previous, kt⟩
  refine ⟨(kt.regs .x3 (by decide)).trans column, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [previous, column, ka.regs .x20 (by decide)]

theorem previous_nat (column q : Nat) (positive : 0 < q) (bound : column < q) :
    (if column = 0 then q else column) - 1 = (column + q - 1) % q := by
  by_cases zero : column = 0
  · simp only [zero, ite_true, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (by omega_using [positive] : q - 1 < q)).symm
  · simp only [zero, ite_false]
    have sub : column + q - 1 - q = column - 1 := by omega_using []
    rw [Nat.mod_eq_sub_mod (by omega_using [zero] : q ≤ column + q - 1), sub,
      Nat.mod_eq_of_lt (by omega_using [bound] : column - 1 < q)]

theorem previous_word_nat (column q : Nat) (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : column < q) :
    (if BitVec.ofNat 64 column = 0#64 then BitVec.ofNat 64 q else BitVec.ofNat 64 column) - 1 =
      BitVec.ofNat 64 ((column + q - 1) % q) := by
  have zero : BitVec.ofNat 64 column = 0#64 ↔
      column = 0 := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound qBound)] at hn
      exact hn
    · intro h; rw [h]
  simp only [zero]
  by_cases h : column = 0
  · simp only [h, ite_true]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat positive, Nat.zero_add, Nat.mod_eq_of_lt (by omega_using [positive] : q - 1 < q)]
  · simp only [h, ite_false]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [h] : 1 ≤ column),
      ← previous_nat _ q positive bound, ite_eq_right h]

theorem code_nat_ok (s : State) (slice segment index q : Nat)
    (hs : s.gpr .x22 = BitVec.ofNat 64 slice)
    (hg : s.gpr .x21 = BitVec.ofNat 64 segment)
    (hi : s.gpr .x23 = BitVec.ofNat 64 index)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q)
    (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : slice * segment + index < q) :
    WP isa code s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (slice * segment + index) ∧
      t.gpr .x0 = BitVec.ofNat 64 ((slice * segment + index + q - 1) % q) ∧
      Divide.Keeps [.x8, .x2, .x3, .x0, .x12, .x13, .x14, .x15] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨column, previous, keeps⟩
  have word : s.gpr .x22 * s.gpr .x21 + s.gpr .x23 =
      BitVec.ofNat 64 (slice * segment + index) := by
    rw [hs, hg, hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  refine ⟨column.trans word, ?_, keeps⟩
  rw [previous, word, hq]
  exact previous_word_nat _ q positive qBound bound

end VG.Proof.Argon2.AArch64.FillColumn
end

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .x22 * s.gpr .x21 + s.gpr .x23

def predecessor (s : State) : Addr :=
  (if column s = 0 then s.gpr .x20 else column s) - 1

def changed : List Reg := [.x8, .x2, .x3, .x0, .x1, .x6, .x7, .x12, .x13, .x14, .x15]

theorem current_ok (s : State) : WP isa current s fun t =>
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x24) (s.gpr .x3) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold current
  refine WP.seq ((currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [pointer, lane, ka.regs .x20 (by decide), ka.regs .x3 (by decide), ka.regs .x4 (by decide), address]

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x24) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x6, .x15] s t := by
  unfold previous
  refine WP.seq ((previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x6 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x5) (s.gpr .x1) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x7, .x15] s t := by
  unfold reference
  refine WP.seq ((referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x7 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), address]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x6 = address (s.gpr .x4) (s.gpr .x24) (column s) (s.gpr .x20) ∧
    t.gpr .x0 = address (s.gpr .x4) (s.gpr .x24) (predecessor s) (s.gpr .x20) ∧
    t.gpr .x1 = address (s.gpr .x4) (s.gpr .x5) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((saveReference_ok s).mono ?_)
  rintro a ⟨refColumn, ka⟩
  refine WP.seq ((FillColumn.code_ok a).mono ?_)
  rintro b ⟨curColumn, prevColumn, kb⟩
  refine WP.seq ((current_ok b).mono ?_)
  rintro c ⟨curPointer, kc⟩
  refine WP.seq ((previous_ok c).mono ?_)
  rintro d ⟨savedCurrent, prevPointer, kd⟩
  refine WP.seq ((reference_ok d).mono ?_)
  rintro e ⟨savedPrevious, refPointer, ke⟩
  refine (finishArgs_ok e).mono ?_
  rintro t ⟨referenceResult, previousResult, kt⟩
  have coords : column a = column s := by
    unfold column
    rw [ka.regs .x22 (by decide), ka.regs .x21 (by decide), ka.regs .x23 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .x6 (by decide), ke.regs .x6 (by decide), savedCurrent, curPointer,
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), curColumn]
    exact congrArg (fun col => address (s.gpr .x4) (s.gpr .x24) col (s.gpr .x20)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .x4 (by decide),
      kc.regs .x24 (by decide), kc.regs .x0 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), prevColumn]
    change address _ _ ((if column a = 0 then a.gpr .x20 else column a) - 1) _ = _
    rw [coords, ka.regs .x20 (by decide), predecessor]
  · rw [referenceResult, refPointer, kd.regs .x4 (by decide), kd.regs .x5 (by decide),
      kd.regs .x1 (by decide), kd.regs .x20 (by decide), kc.regs .x4 (by decide),
      kc.regs .x5 (by decide), kc.regs .x1 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), kb.regs .x5 (by decide), kb.regs .x1 (by decide),
      kb.regs .x20 (by decide), ka.regs .x4 (by decide), ka.regs .x5 (by decide),
      ka.regs .x20 (by decide), refColumn]
  · exact (((((ka.mono (by simp [changed])).trans (kb.mono (by simp [changed]))).trans
      (kc.mono (by simp [changed]))).trans (kd.mono (by simp [changed]))).trans
      (ke.mono (by simp [changed]))).trans (kt.mono (by simp [changed]))

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

def cell (base : Addr) (p : Spec.Argon2.Params) (lane column : Nat) : Addr :=
  off base ((lane * p.laneLen + column) * 1024)

theorem address_nat (base : Addr) (lane column q : Nat) :
    address base (BitVec.ofNat 64 lane) (BitVec.ofNat 64 column) (BitVec.ofNat 64 q) =
      off base ((lane * q + column) * 1024) := by
  unfold address off
  change (BitVec.ofNat 64 lane * BitVec.ofNat 64 q + BitVec.ofNat 64 column) *
    BitVec.ofNat 64 1024 + base = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index refLane refColumn : Nat)
    (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (rl : s.gpr .x5 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa code s fun t =>
      t.gpr .x6 = cell (s.gpr .x4) p lane (slice * p.segmentLen + index) ∧
      t.gpr .x0 = cell (s.gpr .x4) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .x1 = cell (s.gpr .x4) p refLane refColumn ∧ Divide.Keeps changed s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨current, previous, reference, keeps⟩
  have col : column s = BitVec.ofNat 64 (slice * p.segmentLen + index) := by
    unfold column
    rw [position.slice, position.segmentLength, position.index, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  have prev : predecessor s = BitVec.ofNat 64
      ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) := by
    unfold predecessor
    rw [col, position.laneLength]
    have positive := Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum
    have q := Proof.Argon2.laneLen_segments p bounds.lanesPositive
    exact FillColumn.previous_word_nat _ _ (by omega_using [positive, q])
      (Nat.lt_trans bounds.laneLength_bound (by decide))
      (Proof.Argon2.column_lt p bounds.lanesPositive bounds.sliceBound bounds.indexBound)
  refine ⟨?_, ?_, ?_, keeps⟩
  · rw [current, position.current, col, position.laneLength, address_nat]; rfl
  · rw [previous, position.current, prev, position.laneLength, address_nat]; rfl
  · rw [reference, rl, rc, position.laneLength, address_nat]; rfl

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelLayout`. -/
section
/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

structure Layout (p : Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .x19) 16) 8
  matrixWrite : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  matrixWork : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  matrixFrame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  matrixStack : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint (below s.sp 8)
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)
  stackWork : (below s.sp 8).Disjoint ⟨work s, 5120⟩

theorem Layout.of_keeps {p : Params} {s t : State} (h : Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : Layout p t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have matrix' : matrix t = matrix s := by unfold matrix; rw [bp, k.mem]
  have work' : work t = work s := by unfold work; rw [bp, k.mem]
  constructor
  · rw [k.rd, k.wr, bp]; exact h.frameRead
  · rw [k.wr, bp]; exact h.frameWrite
  · rw [matrix', k.wr]; exact h.matrixWrite
  · rw [work', k.wr]; exact h.workWrite
  · rw [matrix', work']; exact h.matrixWork
  · rw [matrix', bp]; exact h.matrixFrame
  · rw [matrix', sp]; exact h.matrixStack
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem cell_sub (p : Params) (base : Addr) (positive : 0 < p.lanes) {lane column : Nat}
    (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Region.Sub ⟨FillPointers.cell base p lane column, 1024⟩ ⟨base, p.blocks * 1024⟩ :=
  Offset.sub_base base (Proof.Argon2.cell_bytes p positive hl hc)

theorem Layout.cell_cover {p : Params} {s : State} (h : Layout p s) (positive : 0 < p.lanes)
    {lane column : Nat} (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩] s.wr := by
  have sub : Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩]
      [⟨matrix s, p.blocks * 1024⟩] := Covers.of_sub (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨matrix s, p.blocks * 1024⟩, by simp, (lane * p.laneLen + column) * 1024,
          rfl, Proof.Argon2.cell_bytes p positive hl hc⟩)
  exact fun a n ha => h.matrixWrite a n (sub a n ha)

theorem compress_ready (p : Params) (s : State) (layout : Layout p s)
    (positive : 0 < p.lanes) (leftLane leftColumn rightLane rightColumn destLane destColumn : Nat)
    (ll : leftLane < p.lanes) (lc : leftColumn < p.laneLen)
    (rl : rightLane < p.lanes) (rc : rightColumn < p.laneLen)
    (dl : destLane < p.lanes) (dc : destColumn < p.laneLen)
    (left : s.gpr .x0 = FillPointers.cell (matrix s) p leftLane leftColumn)
    (right : s.gpr .x1 = FillPointers.cell (matrix s) p rightLane rightColumn)
    (dest : s.gpr .x6 = FillPointers.cell (matrix s) p destLane destColumn) : FillCompress.Ready s := by
  have leftSub := cell_sub p (matrix s) positive ll lc
  have rightSub := cell_sub p (matrix s) positive rl rc
  have destSub := cell_sub p (matrix s) positive dl dc
  have read (lane column : Nat) (hl : lane < p.lanes) (hc : column < p.laneLen) :
      Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩] (s.rd ++ s.wr) := by
    intro a n ha
    obtain ⟨r, hr, hc⟩ := layout.cell_cover positive hl hc a n ha
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  constructor
  · intro d hd
    exact layout.frameRead d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp)
  · exact layout.frameWrite
  · rw [left]; exact read leftLane leftColumn ll lc
  · rw [right]; exact read rightLane rightColumn rl rc
  · rw [dest]; exact layout.cell_cover positive dl dc
  · exact layout.workWrite
  · rw [left]; exact layout.matrixWork.sub_left leftSub
  · rw [right]; exact layout.matrixWork.sub_left rightSub
  · rw [dest]; exact layout.matrixWork.sub_left destSub
  · exact layout.frameWork
  · rw [left]; exact layout.matrixFrame.sub_left leftSub
  · rw [right]; exact layout.matrixFrame.sub_left rightSub
  · rw [dest]; exact layout.matrixFrame.sub_left destSub
  · rw [left]; exact (layout.matrixStack.sub_left leftSub).symm
  · rw [right]; exact (layout.matrixStack.sub_left rightSub).symm
  · exact layout.stackWork
  · rw [dest]; exact layout.matrixStack.sub_left destSub
  · exact layout.frameStack

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat) (ha : d % 8 = 0) (hb : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.load r .x19 d].flatten) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .x19) d) 64 ∧ Divide.Keeps [r] s t := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    Instructions.load_ok s r .x19 d ha hb read

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1
  column : t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.mapping s (Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.mapping Impl.Argon2.AArch64.FillKernel.lanes
  refine WP.seq ((load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .x0 (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .x6 = FillPointers.cell (matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .x0 = FillPointers.cell (matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .x1 = FillPointers.cell (matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .x5 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.AArch64.FillKernel.pointers s (Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.AArch64.FillKernel.pointers Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((load_ok s .x4 232 (by decide) (by decide) (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .x5 = BitVec.ofNat 64 refLane := (keeps.regs .x5 (by decide)).trans laneWord
  have col' : a.gpr .x0 = BitVec.ofNat 64 refColumn := (keeps.regs .x0 (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

end

/-! ### `Argon2.AArch64.FillCompress`, which this module and modules that import it used -/

section

/-! The complete compression/update sequence from allocation and frame invariants. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def writes (s : State) : List Region :=
  [⟨s.gpr .x6, 1024⟩, ⟨work s + 4096, 1024⟩, ⟨work s, 4096⟩,
    below s.sp 8, ⟨off (s.gpr .x19) 16, 8⟩]

structure Done (s t : State) : Prop where
  block : blockAt t.mem (s.gpr .x6) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (s.gpr .x6))
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (writes s) s.mem t.mem

theorem code_ok (s : State) (h : Ready s) : WP isa code s (Done s) := by
  unfold code
  refine WP.seq ((setup_ok s h).mono ?_)
  intro a prepared
  refine (operation_ok a prepared.ready).mono ?_
  intro t done
  refine ⟨?_, fun r hr => (done.regs r hr).trans (prepared.regs r hr),
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, done.sp.trans prepared.sp, ?_⟩
  · have block := done.block
    rw [prepared.oldBlock, prepared.dest, prepared.counter, prepared.leftBlock,
      prepared.rightBlock] at block
    exact block
  · have frame : Frame (writes s) a.mem t.mem := by
      have original := done.frame
      rw [prepared.dest] at original
      simp only [callWrites, prepared.output, prepared.scratch,
        prepared.sp] at original
      exact original.mono (by intro r hr; exact List.mem_append_left _ hr)
    have savedFrame : Frame (writes s) s.mem a.mem := prepared.frame.mono (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      simp [writes])
    exact savedFrame.trans frame

theorem code_sp_ok (s : State) (h : Ready s) :
    WP isa code s fun t => Done s t ∧ t.sp = s.sp :=
  (code_ok s h).mono (fun _ done => ⟨done, done.sp⟩)

end VG.Proof.Argon2.AArch64.FillCompress

end

end

/-! ### `Argon2.AArch64.FillKernelSpec`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.FillKernel`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.FillKernelPrepare`, which only this module used -/

section

/-! Complete active-cell update from a random word and the matrix allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def currentColumn (p : Params) (slice index : Nat) : Nat := slice * p.segmentLen + index

def previousColumn (p : Params) (slice index : Nat) : Nat :=
  (currentColumn p slice index + p.laneLen - 1) % p.laneLen

def current (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (matrix s) p lane (currentColumn p slice index)

def previous (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (matrix s) p lane (previousColumn p slice index)

def referenced (s : State) (p : Params) (pass lane slice index : Nat) : Addr :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  FillPointers.cell (matrix s) p ref.1 ref.2

structure Prepared (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  ready : FillCompress.Ready t
  currentPtr : t.gpr .x6 = current s p lane slice index
  previousPtr : t.gpr .x0 = previous s p lane slice index
  referencePtr : t.gpr .x1 = referenced s p pass lane slice index
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem prepare_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.prepare s (Prepared s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.prepare
  refine WP.seq ((mapping_ok s p pass lane slice index h).mono ?_)
  intro a mapped
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  refine ((pointers_ok a p pass lane slice index ref.1 ref.2
    (h.layout.of_keeps mapped.keeps) h.bounds (h.position.of_keeps mapped.keeps)
    mapped.selected mapped.column).mono ?_)
  intro b pointers
  have keeps := mapped.keeps.trans pointers.keeps
  have matrixA : matrix a = matrix s := by
    unfold matrix; rw [mapped.keeps.mem, mapped.keeps.regs .x19 (by decide)]
  have matrixB : matrix b = matrix a := by
    unfold matrix; rw [pointers.keeps.mem, pointers.keeps.regs .x19 (by decide)]
  have cur : b.gpr .x6 = current s p lane slice index := by
    rw [pointers.current, matrixA]; rfl
  have prev : b.gpr .x0 = previous s p lane slice index := by
    rw [pointers.previous, matrixA]; rfl
  have other : b.gpr .x1 = referenced s p pass lane slice index := by
    rw [pointers.reference, matrixA]; rfl
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have previousBound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  obtain ⟨refLane, refColumn⟩ := Proof.Argon2.reference_bounds p h.bounds.lanesPositive
    h.bounds.memoryMinimum pass lane slice index (s.gpr .x0) h.bounds.laneBound
  have compressReady : FillCompress.Ready b := by
    apply compress_ready p b (h.layout.of_keeps keeps) h.bounds.lanesPositive
      lane (previousColumn p slice index) ref.1 ref.2 lane (currentColumn p slice index)
      h.bounds.laneBound previousBound refLane refColumn h.bounds.laneBound columnBound
    · rw [pointers.previous, matrixB]; rfl
    · rw [pointers.reference, matrixB]
    · rw [pointers.current, matrixB]; rfl
  exact ⟨compressReady, cur, prev, other, keeps⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

end


/-! Complete active-cell update from a random word and the matrix allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) (lane slice index : Nat) : List Region :=
  [⟨current s p lane slice index, 1024⟩, ⟨work s, 5120⟩,
    below s.sp 8, ⟨off (s.gpr .x19) 16, 8⟩]

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  block : blockAt t.mem (current s p lane slice index) =
    let next := Spec.Argon2.compress (blockAt s.mem (previous s p lane slice index))
      (blockAt s.mem (referenced s p pass lane slice index))
    if pass = 0 then next else xorBlock next (blockAt s.mem (current s p lane slice index))
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p lane slice index) s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.code s (Done s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.code
  refine WP.seq ((prepare_ok s p pass lane slice index h).mono ?_)
  intro b prepared
  have keeps := prepared.keeps
  have cur := prepared.currentPtr
  have prev := prepared.previousPtr
  have other := prepared.referencePtr
  refine (FillCompress.code_sp_ok b prepared.ready).mono ?_
  rintro t ⟨done, mx⟩
  have counter : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [keeps.mem, keeps.regs .x19 (by decide)]
    exact h.passWord
  refine ⟨?_, ?_, done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, mx.trans keeps.sp⟩
  · have block := done.block
    rw [cur, prev, other, keeps.mem, counter] at block
    simp only [ReferenceMap.word_zero pass (Nat.lt_trans h.bounds.passBound (by decide))] at block
    exact block
  · intro r hr
    have ne : r ∉ ReferenceMap.changed := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (done.regs r hr).trans (keeps.regs r ne)
  · have workB : FillCompress.work b = work s := by
      unfold FillCompress.work work
      rw [keeps.regs .x19 (by decide), keeps.mem]
    have frame := done.frame
    rw [FillCompress.writes, workB, cur, keeps.sp, keeps.regs .x19 (by decide), keeps.mem] at frame
    change Frame [⟨current s p lane slice index, 1024⟩, ⟨work s + 4096, 1024⟩,
      ⟨work s, 4096⟩, below s.sp 8, ⟨off (s.gpr .x19) 16, 8⟩] s.mem t.mem at frame
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [writes], fun _ h => h⟩
    · exact ⟨⟨work s, 5120⟩, by simp [writes], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨work s, 5120⟩, by simp [writes], Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp [writes], fun _ h => h⟩
    · exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

end

/-! Merged from `Proof.Argon2.AArch64.FillKernelMatrix`. -/

@[expose] public section

section
/-! The filling step updates exactly one cell of the specification's block array. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def currentIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + currentColumn p slice index

def previousIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + previousColumn p slice index

def referenceIndex (s : State) (p : Params) (pass lane slice index : Nat) : Nat :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  ref.1 * p.laneLen + ref.2

def nextBlock (s : State) (p : Params) (pass lane slice index : Nat) (blocks : Array Block) : Block :=
  let next := Spec.Argon2.compress (blocks[previousIndex p lane slice index]?.getD zeroBlock)
    (blocks[referenceIndex s p pass lane slice index]?.getD zeroBlock)
  if pass = 0 then next else xorBlock next (blocks[currentIndex p lane slice index]?.getD zeroBlock)

theorem Done.represents {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : Ready p pass lane slice index s) (done : Done s t p pass lane slice index)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (matrix s) p.blocks
      (blocks.set! (currentIndex p lane slice index) (nextBlock s p pass lane slice index blocks)) := by
  have currentBound := Proof.Argon2.current_cell_lt p ready.bounds.lanesPositive
    ready.bounds.laneBound ready.bounds.sliceBound ready.bounds.indexBound
  have previousBound := Proof.Argon2.previous_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum ready.bounds.laneBound (column := currentColumn p slice index)
  have referenceBound := Proof.Argon2.reference_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum pass lane slice index (s.gpr .x0) ready.bounds.laneBound
  apply represented.update (currentIndex p lane slice index) currentBound (nextBlock s p pass lane slice index blocks)
  · have block := done.block
    change blockAt t.mem (Proof.Argon2.matrixCell (matrix s) (currentIndex p lane slice index)) = _ at block
    have prev := represented.block (previousIndex p lane slice index) previousBound
    have other := represented.block (referenceIndex s p pass lane slice index) referenceBound
    have old := represented.block (currentIndex p lane slice index) currentBound
    change blockAt s.mem (previous s p lane slice index) = _ at prev
    change blockAt s.mem (referenced s p pass lane slice index) = _ at other
    change blockAt s.mem (current s p lane slice index) = _ at old
    rw [prev, other, old] at block
    exact block
  · intro j hj different
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have blocksBound := Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) ready.bounds.memoryBound
      exact Proof.Argon2.matrixCell_disjoint _ p.blocks j (currentIndex p lane slice index)
        (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right blocksBound (by decide)) (by decide)) hj currentBound different
    · exact ready.layout.matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact ready.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)).sub_right
        (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Relate the complete assembly step to the reviewed filling-state transition. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem update_spec (s : State) (p : Params) (pass lane slice index : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (random : s.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    state.memory.set! (currentIndex p lane slice index) (nextBlock s p pass lane slice index state.memory) =
      (fillBlock p pass slice lane index state).memory := by
  rw [Proof.Argon2.FillStep.memory p pass lane slice index state active]
  unfold nextBlock referenceIndex
  rw [random]
  rfl

theorem code_spec_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory)
    (random : s.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    WP isa Impl.Argon2.AArch64.FillKernel.code s fun t => Done s t p pass lane slice index ∧
      Proof.Argon2.Represents t.mem (matrix s) p.blocks (fillBlock p pass slice lane index state).memory := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t done
  have represented' := done.represents ready state.memory represented
  rw [update_spec s p pass lane slice index state ready.bounds.active random] at represented'
  exact ⟨done, represented'⟩

end VG.Proof.Argon2.AArch64.FillKernel

end

end

/-! Merged from `Proof.Argon2.AArch64.DependentWordPointer`. -/

@[expose] public section

section
/-! The data-dependent word's address is the specification's cyclic predecessor. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem args_ok (s : State) : WP isa (.block args) s fun t =>
    t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x8 = s.gpr .x24 ∧ Divide.Keeps [.x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [args, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa pointer s fun t =>
      t.gpr .x8 = FillKernel.previous s p lane slice index ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold pointer Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((FillKernel.load_ok s .x4 232 (by decide) (by decide) (h.layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, ka⟩
  have k : Divide.Keeps ReferenceMap.changed s a := ka.mono (by decide)
  have pos := h.position.of_keeps k
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have segment := Proof.Argon2.segmentLen_ge_two p h.bounds.lanesPositive h.bounds.memoryMinimum
  have q := Proof.Argon2.laneLen_segments p h.bounds.lanesPositive
  refine WP.seq ((FillColumn.code_nat_ok a slice p.segmentLen index p.laneLen
    pos.slice pos.segmentLength pos.index pos.laneLength (by omega_using [columnBound])
    (Nat.lt_trans h.bounds.laneLength_bound (by decide)) columnBound).mono ?_)
  rintro b ⟨_, prev, kb⟩
  refine WP.seq ((args_ok b).mono ?_)
  rintro c ⟨col, laneReg, kc⟩
  have col' := col.trans prev
  have lane' : c.gpr .x8 = BitVec.ofNat 64 lane := laneReg.trans ((kb.regs .x24 (by decide)).trans pos.current)
  have length : c.gpr .x20 = BitVec.ofNat 64 p.laneLen :=
    (kc.regs .x20 (by decide)).trans ((kb.regs .x20 (by decide)).trans pos.laneLength)
  refine (BlockAddress.code_nat_ok c lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) p.laneLen lane' col' length).mono ?_
  rintro t ⟨address, kt⟩
  refine ⟨?_, ((k.trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [address, kc.regs .x4 (by decide), kb.regs .x4 (by decide), base]
  rfl

end VG.Proof.Argon2.AArch64.DependentWord
end

/-! Select the specified secret random word from the public previous-cell address. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem read_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .x8) 8) :
    WP isa (.block Impl.Argon2.AArch64.DependentWord.read) s fun t => t.gpr .x0 = s.mem.readW (s.gpr .x8) 64 ∧ Divide.Keeps [.x0] s t := by
  simpa only [Impl.Argon2.AArch64.DependentWord.read,
    List.flatten_cons, List.flatten_nil, List.append_nil, BitVec.add_zero]
    using Instructions.load_ok s .x0 .x8 0 (by decide) (by decide)
      (by simpa only [BitVec.add_zero] using hr)

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa code s fun t =>
      t.gpr .x0 = (blockAt s.mem (FillKernel.previous s p lane slice index))[0] ∧
      Divide.Keeps ReferenceMap.changed s t := by
  unfold code
  refine WP.seq ((pointer_ok s p pass lane slice index h).mono ?_)
  rintro a ⟨pointer, keeps⟩
  have bound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  have cover := h.layout.cell_cover h.bounds.lanesPositive h.bounds.laneBound bound
  have hr : InRegions (a.rd ++ a.wr) (a.gpr .x8) 8 := by
    rw [keeps.rd, keeps.wr, pointer]
    have contains : (⟨FillKernel.previous s p lane slice index, 1024⟩ : Region).Contains
        (FillKernel.previous s p lane slice index) 8 :=
      by simpa only [BitVec.add_zero] using (Offset.contains_base
        (FillKernel.previous s p lane slice index) (d := 0) (n := 8) (k := 1024) (by decide) (by decide))
    obtain ⟨r, hr, hc⟩ := cover _ _ ⟨⟨FillKernel.previous s p lane slice index, 1024⟩,
      by simp [FillKernel.previous, FillKernel.previousColumn, FillKernel.currentColumn], contains⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (read_ok a hr).mono ?_
  rintro t ⟨random, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [random, pointer, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨0, by decide⟩ : Fin 128)]
  rw [blockAt_get]
  change s.mem.readW _ 64 = s.mem.readW (_ + 0#64) 64
  rw [BitVec.add_zero]

theorem code_spec_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa code s fun t =>
      t.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (code_ok s p pass lane slice index h).mono ?_
  rintro t ⟨random, keeps⟩
  have bound := Proof.Argon2.previous_cell_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    h.bounds.laneBound (column := FillKernel.currentColumn p slice index)
  have block := represented.block (FillKernel.previousIndex p lane slice index) bound
  change blockAt s.mem (FillKernel.previous s p lane slice index) = _ at block
  rw [block] at random
  refine ⟨?_, keeps⟩
  simpa only [Proof.Argon2.FillStep.random, dependent, Bool.false_eq_true, ite_false, FillKernel.previousIndex, FillKernel.previousColumn,
    FillKernel.currentColumn] using random

end VG.Proof.Argon2.AArch64.DependentWord
