module

public import VerifiedGarbage.Impl.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.FillStep
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
public import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel
public import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Argon2.X86_64.Wrap
import VerifiedGarbage.Proof.Argon2.Reference
public import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Argon2.X86_64.Wrap
meta import VerifiedGarbage.Proof.Argon2.Reference
meta import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Argon2.X86_64.Relative
import VerifiedGarbage.Proof.Argon2.X86_64.Mix
meta import VerifiedGarbage.Impl.Argon2.X86_64.Relative
meta import VerifiedGarbage.Proof.Argon2.X86_64.Mix
public import VerifiedGarbage.Proof.Argon2.X86_64.Divide
import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT
meta import VerifiedGarbage.Proof.Argon2.X86_64.Divide
meta import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceCount
public import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceCount
meta import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Argon2.X86_64.FillKernelArgs`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.ReferenceMapLane`, which only this module used -/

section

/-! ### `Argon2.X86_64.ReferenceMapState`, which only this module used -/

section

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapArgs`. -/

@[expose] public section

section
/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem pass_ea (s : State) : s.ea { base := .rbp } = s.gpr .rbp := by
  change s.gpr .rbp + 0#64 = s.gpr .rbp
  exact BitVec.add_zero _

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .r9 = s.mem.readW (s.gpr .rbp) 64 ∧ Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [loadPass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    pass_ea, State.load64, read, ite_true, Option.map_some, RegUpd.gpr_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .rdi = s.gpr .r8 ∧ t.gpr .rsi = s.gpr .rbx ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .r9 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .r11 ∧ t.gpr .rsi = s.gpr .r8 ∧
    Divide.Keeps [.r9, .rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .rdi = s.gpr .rax + s.gpr .r10 ∧ t.gpr .rsi = s.gpr .r12 ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Parameters and register invariants for the complete reference mapping. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64

/-- Every stage preserves the enclosing loop's callee-saved registers. -/
def changed : List Reg := [.rax, .rdx, .rcx, .r8, .r9, .r10, .r11, .rdi, .rsi]

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
  current : s.gpr .rbx = BitVec.ofNat 64 lane
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  slice : s.gpr .r14 = BitVec.ofNat 64 slice
  index : s.gpr .r15 = BitVec.ofNat 64 index

theorem Position.of_keeps {s t : State} {p : Spec.Argon2.Params} {lane slice index : Nat}
    (h : Position p lane slice index s) (k : Divide.Keeps changed s t) :
    Position p lane slice index t :=
  ⟨(k.regs .rbx (by decide)).trans h.current,
    (k.regs .r12 (by decide)).trans h.laneLength,
    (k.regs .r13 (by decide)).trans h.segmentLength,
    (k.regs .r14 (by decide)).trans h.slice,
    (k.regs .r15 (by decide)).trans h.index⟩

structure Ready (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s : State) : Prop where
  bounds : Bounds p pass lane slice index
  position : Position p lane slice index s
  lanes : s.gpr .rsi = BitVec.ofNat 64 p.lanes
  passRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8
  passWord : s.mem.readW (s.gpr .rbp) 64 = BitVec.ofNat 64 pass

theorem Ready.lanes_nat {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s : State}
    (h : Ready p pass lane slice index s) : (s.gpr .rsi).toNat = p.lanes := by
  rw [h.lanes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bounds.lanesBound (by decide))]

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : Ready p pass lane slice index s) (k : Divide.Keeps changed s t)
    (lanes : t.gpr .rsi = s.gpr .rsi) : Ready p pass lane slice index t := by
  refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanes, ?_, ?_⟩
  · rw [k.rd, k.wr, k.regs .rbp (by decide)]
    exact h.passRead
  · rw [k.mem, k.regs .rbp (by decide)]
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

end VG.Proof.Argon2.X86_64.ReferenceMap

end

end

/-! Merged from `Proof.Argon2.X86_64.ReferenceLane`. -/

@[expose] public section

section
/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.X86_64.ReferenceLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceLane

structure Prefix (s t : State) : Prop where
  high : t.gpr .rdi = s.gpr .rdi >>> 32
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps [.rdi, .r11] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

def changed : List Reg := [.rdi, .r11] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .r8).toNat = (s.gpr .rdi >>> 32).toNat % (s.gpr .rsi).toNat ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .rsi (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .rdi) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .r11 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun _ _ => True) (.block highArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceLane
end

/-! Merged from `Proof.Argon2.X86_64.FirstLane`. -/
section
/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.zf = decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0) ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change (s.gpr .r9 ||| s.gpr .r14) = 0#64 ↔ _
    exact BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .r8 = s.gpr .rbx ∧ Divide.Keeps [.r8] s t := by
  apply WP.of_runBlock
  simp only [current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r8 = (if s.gpr .r9 = 0 ∧ s.gpr .r14 = 0 then s.gpr .rbx else s.gpr .r8) ∧
    Divide.Keeps [.rax, .r8] s t := by
  unfold code
  refine WP.seq ((test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0))
    (by simp only [eval, flag]) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .rbx (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .r8 (by decide)

end VG.Proof.Argon2.X86_64.FirstLane
end

/-! Choose the reference lane, restore the pass and prepare the window inputs. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Chosen (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r8 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  pass : t.gpr .r9 = BitVec.ofNat 64 pass
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem chooseLane_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa chooseLane s (Chosen p pass lane slice index s) := by
  have lanesNat : (s.gpr .rsi).toNat = p.lanes := by
    rw [ready.lanes, word_nat _ (by have := ready.bounds.lanesBound; omega_using [this])]
  unfold chooseLane
  refine WP.seq ((ReferenceLane.code_ok s
    (by rw [lanesNat]; exact ready.bounds.lanesPositive)
    (by rw [lanesNat]; exact ready.bounds.lanesBound)).mono ?_)
  rintro a ⟨laneNat, original, ka⟩
  have ka' : Divide.Keeps changed s a := ka.mono (by decide)
  have readA : InRegions (a.rd ++ a.wr) (a.gpr .rbp) 8 := by
    rw [ka'.rd, ka'.wr, ka'.regs .rbp (by decide)]
    exact ready.passRead
  have laneWord : a.gpr .r8 = BitVec.ofNat 64 ((s.gpr .rdi >>> 32).toNat % p.lanes) := by
    calc
      a.gpr .r8 = BitVec.ofNat 64 (a.gpr .r8).toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [laneNat, lanesNat]
  refine WP.seq ((loadPass_ok a readA).mono ?_)
  rintro b ⟨loaded, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kab := ka'.trans kb'
  have pb := ready.position.of_keeps kab
  have passWord : b.gpr .r9 = BitVec.ofNat 64 pass := by
    rw [loaded, ka'.mem, ka'.regs .rbp (by decide)]
    exact ready.passWord
  have passZero : b.gpr .r9 = 0 ↔ pass = 0 := by
    rw [passWord]
    exact word_zero _ (by have := ready.bounds.passBound; omega_using [this])
  have sliceZero : b.gpr .r14 = 0 ↔ slice = 0 := by
    rw [pb.slice]
    exact word_zero _ (by have := ready.bounds.sliceBound; omega_using [this])
  refine (FirstLane.code_ok b).mono ?_
  rintro t ⟨out, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ready.position.of_keeps (kab.trans kt'), kab.trans kt'⟩
  · rw [out]
    by_cases position : pass = 0 ∧ slice = 0 <;>
      simp only [passZero, sliceZero, pb.current, kb.regs .r8 (by decide), laneWord,
        chosenLane, position, and_self, ite_true, ite_false]
  · exact (kt.regs .r9 (by decide)).trans passWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans original)

structure Prepared (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  pass : (t.gpr .r9).toNat = pass
  original : t.gpr .r11 = s.gpr .rdi
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
    (kt.regs .r11 (by decide)).trans ha.original,
    ha.position.of_keeps kt', ha.keeps.trans kt'⟩
  rw [kt.regs .r9 (by decide), ha.pass, word_nat _ (by have := ready.bounds.passBound; omega_using [this])]

end VG.Proof.Argon2.X86_64.ReferenceMap

end

end

/-! ### `Argon2.X86_64.Relative`, which this module and modules that import it used -/

section

/-! # The baseline reference-window mapping is fixed time and preserves memory -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Relative

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Relative

def value (random count : Addr) : Addr :=
  let j := random &&& 0xffffffff
  let x := (j * j) >>> 32
  let y := (x * count) >>> 32
  count - 1 - y

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rax = value (s.gpr .rdi) (s.gpr .rsi) ∧
    (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, readSrc, State.setReg32, execMul, execAlu, execShift,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, and_self, ite_true, ite_false,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨?_, ?_, trivial⟩
  · rw [VG.Proof.Argon2.X86_64.low32]; rfl
  · intro r h1 h2 h3
    simp only [h1, h2, h3, ite_false]

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

theorem code_nat_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (value_nat _ _ lo bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Relative

end

end

/-! ### `Argon2.X86_64.Wrap`, which this module and modules that import it used -/

section

/-! # Masked subtraction agrees with wrapping the reference column -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Wrap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Wrap

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rdi = (if (s.gpr .rdi).toNat < (s.gpr .rsi).toNat
      then s.gpr .rdi else s.gpr .rdi - s.gpr .rsi) ∧
    Divide.Keeps [.rdi, .r10, .rax] s t := by
  unfold code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg,     RegUpd.gpr_arithFlags,     RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, Divide.select_value, decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]
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

theorem code_nat_ok (s : State) (bound : (s.gpr .rdi).toNat < 2 * (s.gpr .rsi).toNat) :
    WP isa code s fun t =>
      t.gpr .rdi = BitVec.ofNat 64 ((s.gpr .rdi).toNat % (s.gpr .rsi).toNat) ∧
      Divide.Keeps [.rdi, .r10, .rax] s t :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (wrap_nat _ _ bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Wrap

end

end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapWindow`. -/

@[expose] public section

section
/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  count : t.gpr .r8 = BitVec.ofNat 64 (windowSize p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
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
  have passB : (b.gpr .r9).toNat = pass := by
    rw [kb.regs .r9 (by decide), prepared.pass]
  have same : decide (b.gpr .rdi = b.gpr .rsi) =
      (chosenLane p pass lane slice (s.gpr .rdi) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .rdi (by decide), kb.regs .rsi (by decide), prepared.selected, prepared.current]
    exact word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .rdi (by decide)).trans ((kb.regs .rdi (by decide)).trans prepared.selected)
  · exact (kt.regs .rsi (by decide)).trans ((kb.regs .rsi (by decide)).trans prepared.current)
  · simpa only [windowSize, same] using countWord
  · exact (kt.regs .r10 (by decide)).trans startWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans prepared.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapRelative`. -/
section
/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.Relative.code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.rax, .rdx, .rcx] s t := by
  refine WP.mono_mx (by decide +kernel) (Relative.code_nat_ok s positive bound) ?_
  rintro t ⟨out, other, mem, rd, wr⟩ mx
  refine ⟨out, ⟨?_, mem, rd, wr, mx⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  relative : t.gpr .rax = BitVec.ofNat 64 (relativeValue p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (counted : Counted p pass lane slice index s a) :
    WP isa relative a (Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .rsi).toNat = windowSize p pass lane slice index (s.gpr .rdi) := by
    rw [count, counted.count, word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .rdi = s.gpr .rdi := random.trans counted.original
  refine (relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans (selected.trans counted.selected)
  · simpa only [relativeValue, countNat, randomWord] using out
  · exact (kt.regs .r10 (by decide)).trans ((kb.regs .r10 (by decide)).trans counted.start)
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans counted.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapFinish`. -/
section
/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  column : t.gpr .rdi = BitVec.ofNat 64
    ((windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)) % p.laneLen)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (mapped : Mapped p pass lane slice index s a) :
    WP isa finish a (Result p pass lane slice index s) := by
  unfold finish
  refine WP.seq ((wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .rdi = BitVec.ofNat 64
      (windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .rdi)
    have q := bounds.laneLength_bound
    omega_using [small, q]
  have sumNat : (b.gpr .rdi).toNat =
      windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi) := by
    rw [sumWord, word_nat _ sumBound]
  have lengthNat : (b.gpr .rsi).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans ((kb.regs .r9 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans mapped.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMap`. -/
section
/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

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
      t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1 ∧
      t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2 ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps changed s t := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [spec_lane, spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.FillPointersNat`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPointersArgs`. -/
section
/-! Short register-setup steps for the filling pointers. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

theorem saveReference_ok (s : State) : WP isa (.block saveReference) s fun t =>
    t.gpr .rsi = s.gpr .rdi ∧ Divide.Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [saveReference, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem currentArgs_ok (s : State) : WP isa (.block currentArgs) s fun t =>
    t.gpr .rax = s.gpr .rbx ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [currentArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem previousArgs_ok (s : State) : WP isa (.block previousArgs) s fun t =>
    t.gpr .r10 = s.gpr .rax ∧ t.gpr .rcx = s.gpr .rdi ∧ t.gpr .rax = s.gpr .rbx ∧
    Divide.Keeps [.r10, .rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [previousArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem referenceArgs_ok (s : State) : WP isa (.block referenceArgs) s fun t =>
    t.gpr .r11 = s.gpr .rax ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .rax = s.gpr .r9 ∧
    Divide.Keeps [.r11, .rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [referenceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finishArgs_ok (s : State) : WP isa (.block finishArgs) s fun t =>
    t.gpr .rsi = s.gpr .rax ∧ t.gpr .rdi = s.gpr .r11 ∧
    Divide.Keeps [.rsi, .rdi] s t := by
  apply WP.of_runBlock
  simp only [finishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillPointers`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillColumn`. -/
section
/-! Current-column arithmetic and the cyclic predecessor, preserving the
matrix, enclosing loop registers and MXCSR. -/

namespace VG.Proof.Argon2.X86_64.FillColumn

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillColumn

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .rcx = s.gpr .r14 * s.gpr .r13 + s.gpr .r15 ∧
    Divide.Keeps [.rax, .rdx, .rcx] s t := by
  apply WP.of_runBlock
  simp only [current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .rcx (.imm 0)]) s
    fun t => t.zf = decide (s.gpr .rcx = 0) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl]
  refine ⟨?_, ?_⟩
  · change (s.gpr .rcx - 0#64 == 0#64) = decide (s.gpr .rcx = 0#64)
    rw [BitVec.sub_zero]
    exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

theorem move_ok (s : State) (r : Reg) : WP isa (.block [.mov .rdi (.reg r)]) s
    fun t => t.gpr .rdi = s.gpr r ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

theorem decrement_ok (s : State) : WP isa (.block [.alu .sub .rdi (.imm 1)]) s
    fun t => t.gpr .rdi = s.gpr .rdi - 1 ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .rdi = (if s.gpr .rcx = 0 then s.gpr .r12 else s.gpr .rcx) - 1 ∧
    Divide.Keeps [.rdi] s t := by
  unfold previous
  refine WP.seq ((compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have selected : WP isa select a fun b =>
      b.gpr .rdi = (if s.gpr .rcx = 0 then s.gpr .r12 else s.gpr .rcx) ∧
      Divide.Keeps [.rdi] s b := by
    unfold select
    refine WP.ite (decide (s.gpr .rcx = 0)) (by simp only [eval, flag]) ?_ ?_
    · intro h
      have zero := of_decide_eq_true h
      refine (move_ok a .r12).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .r12 (by simp), ite_eq_left zero],
        (ka.mono (by simp)).trans kb⟩
    · intro h
      have nonzero := of_decide_eq_false h
      refine (move_ok a .rcx).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .rcx (by simp), ite_eq_right nonzero],
        (ka.mono (by simp)).trans kb⟩
  refine WP.seq (selected.mono ?_)
  rintro b ⟨value, kb⟩
  refine (decrement_ok b).mono ?_
  rintro t ⟨result, kt⟩
  exact ⟨by rw [result, value], kb.trans kt⟩

theorem code_ok (s : State) : WP isa code s fun t =>
    let column := s.gpr .r14 * s.gpr .r13 + s.gpr .r15
    t.gpr .rcx = column ∧
    t.gpr .rdi = (if column = 0 then s.gpr .r12 else column) - 1 ∧
    Divide.Keeps [.rax, .rdx, .rcx, .rdi] s t := by
  unfold code
  refine WP.seq ((current_ok s).mono ?_)
  rintro a ⟨column, ka⟩
  refine (previous_ok a).mono ?_
  rintro t ⟨previous, kt⟩
  refine ⟨(kt.regs .rcx (by decide)).trans column, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [previous, column, ka.regs .r12 (by decide)]

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
    (hs : s.gpr .r14 = BitVec.ofNat 64 slice)
    (hg : s.gpr .r13 = BitVec.ofNat 64 segment)
    (hi : s.gpr .r15 = BitVec.ofNat 64 index)
    (hq : s.gpr .r12 = BitVec.ofNat 64 q)
    (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : slice * segment + index < q) :
    WP isa code s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 (slice * segment + index) ∧
      t.gpr .rdi = BitVec.ofNat 64 ((slice * segment + index + q - 1) % q) ∧
      Divide.Keeps [.rax, .rdx, .rcx, .rdi] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨column, previous, keeps⟩
  have word : s.gpr .r14 * s.gpr .r13 + s.gpr .r15 =
      BitVec.ofNat 64 (slice * segment + index) := by
    rw [hs, hg, hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  refine ⟨column.trans word, ?_, keeps⟩
  rw [previous, word, hq]
  exact previous_word_nat _ q positive qBound bound

end VG.Proof.Argon2.X86_64.FillColumn
end

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .r14 * s.gpr .r13 + s.gpr .r15

def predecessor (s : State) : Addr :=
  (if column s = 0 then s.gpr .r12 else column s) - 1

def changed : List Reg := [.rax, .rdx, .rcx, .rdi, .rsi, .r10, .r11]

theorem current_ok (s : State) : WP isa current s fun t =>
    t.gpr .rax = address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rcx) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold current
  refine WP.seq ((currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by simp)).trans kt⟩
  rw [pointer, lane, ka.regs .r12 (by decide), ka.regs .rcx (by decide), ka.regs .r8 (by decide), address]

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .r10 = s.gpr .rax ∧
    t.gpr .rax = address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rdi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r10] s t := by
  unfold previous
  refine WP.seq ((previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r10 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .r11 = s.gpr .rax ∧
    t.gpr .rax = address (s.gpr .r8) (s.gpr .r9) (s.gpr .rsi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r11] s t := by
  unfold reference
  refine WP.seq ((referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r11 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), address]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r10 = address (s.gpr .r8) (s.gpr .rbx) (column s) (s.gpr .r12) ∧
    t.gpr .rdi = address (s.gpr .r8) (s.gpr .rbx) (predecessor s) (s.gpr .r12) ∧
    t.gpr .rsi = address (s.gpr .r8) (s.gpr .r9) (s.gpr .rdi) (s.gpr .r12) ∧
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
    rw [ka.regs .r14 (by decide), ka.regs .r13 (by decide), ka.regs .r15 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .r10 (by decide), ke.regs .r10 (by decide), savedCurrent, curPointer,
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), curColumn]
    exact congrArg (fun col => address (s.gpr .r8) (s.gpr .rbx) col (s.gpr .r12)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .r8 (by decide),
      kc.regs .rbx (by decide), kc.regs .rdi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), prevColumn]
    change address _ _ ((if column a = 0 then a.gpr .r12 else column a) - 1) _ = _
    rw [coords, ka.regs .r12 (by decide), predecessor]
  · rw [referenceResult, refPointer, kd.regs .r8 (by decide), kd.regs .r9 (by decide),
      kd.regs .rsi (by decide), kd.regs .r12 (by decide), kc.regs .r8 (by decide),
      kc.regs .r9 (by decide), kc.regs .rsi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), kb.regs .r9 (by decide), kb.regs .rsi (by decide),
      kb.regs .r12 (by decide), ka.regs .r8 (by decide), ka.regs .r9 (by decide),
      ka.regs .r12 (by decide), refColumn]
  · exact (((((ka.mono (by simp [changed])).trans (kb.mono (by simp [changed]))).trans
      (kc.mono (by simp [changed]))).trans (kd.mono (by simp [changed]))).trans
      (ke.mono (by simp [changed]))).trans (kt.mono (by simp [changed]))

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

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
    (rl : s.gpr .r9 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa code s fun t =>
      t.gpr .r10 = cell (s.gpr .r8) p lane (slice * p.segmentLen + index) ∧
      t.gpr .rdi = cell (s.gpr .r8) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .rsi = cell (s.gpr .r8) p refLane refColumn ∧ Divide.Keeps changed s t := by
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

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelLayout`. -/
section
/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

structure Layout (p : Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  matrixWrite : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  matrixWork : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  matrixFrame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  matrixStack : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 5120⟩

theorem Layout.of_keeps {p : Params} {s t : State} (h : Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : Layout p t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
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
    (left : s.gpr .rdi = FillPointers.cell (matrix s) p leftLane leftColumn)
    (right : s.gpr .rsi = FillPointers.cell (matrix s) p rightLane rightColumn)
    (dest : s.gpr .r10 = FillPointers.cell (matrix s) p destLane destColumn) : FillCompress.Ready s := by
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

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block [.mov r (.mem (Impl.Argon2.X86_64.at_ .rbp d))]) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .rbp) d) 64 ∧ Divide.Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, read, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1
  column : t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.mapping s (Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.mapping
  refine WP.seq ((load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .rdi (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .r10 = FillPointers.cell (matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .rdi = FillPointers.cell (matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .rsi = FillPointers.cell (matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .r9 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.X86_64.FillKernel.pointers s (Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.X86_64.FillKernel.pointers
  refine WP.seq ((load_ok s .r8 232 (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .r9 = BitVec.ofNat 64 refLane := (keeps.regs .r9 (by decide)).trans laneWord
  have col' : a.gpr .rdi = BitVec.ofNat 64 refColumn := (keeps.regs .rdi (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

end

/-! ### `Argon2.X86_64.FillKernelSpec`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.FillKernel`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.FillKernelPrepare`, which only this module used -/

section

/-! Complete active-cell update from a random word and the matrix allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def currentColumn (p : Params) (slice index : Nat) : Nat := slice * p.segmentLen + index

def previousColumn (p : Params) (slice index : Nat) : Nat :=
  (currentColumn p slice index + p.laneLen - 1) % p.laneLen

def current (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (matrix s) p lane (currentColumn p slice index)

def previous (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (matrix s) p lane (previousColumn p slice index)

def referenced (s : State) (p : Params) (pass lane slice index : Nat) : Addr :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  FillPointers.cell (matrix s) p ref.1 ref.2

structure Prepared (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  ready : FillCompress.Ready t
  currentPtr : t.gpr .r10 = current s p lane slice index
  previousPtr : t.gpr .rdi = previous s p lane slice index
  referencePtr : t.gpr .rsi = referenced s p pass lane slice index
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem prepare_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.prepare s (Prepared s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.prepare
  refine WP.seq ((mapping_ok s p pass lane slice index h).mono ?_)
  intro a mapped
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  refine ((pointers_ok a p pass lane slice index ref.1 ref.2
    (h.layout.of_keeps mapped.keeps) h.bounds (h.position.of_keeps mapped.keeps)
    mapped.selected mapped.column).mono ?_)
  intro b pointers
  have keeps := mapped.keeps.trans pointers.keeps
  have matrixA : matrix a = matrix s := by
    unfold matrix; rw [mapped.keeps.mem, mapped.keeps.regs .rbp (by decide)]
  have matrixB : matrix b = matrix a := by
    unfold matrix; rw [pointers.keeps.mem, pointers.keeps.regs .rbp (by decide)]
  have cur : b.gpr .r10 = current s p lane slice index := by
    rw [pointers.current, matrixA]; rfl
  have prev : b.gpr .rdi = previous s p lane slice index := by
    rw [pointers.previous, matrixA]; rfl
  have other : b.gpr .rsi = referenced s p pass lane slice index := by
    rw [pointers.reference, matrixA]; rfl
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have previousBound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  obtain ⟨refLane, refColumn⟩ := Proof.Argon2.reference_bounds p h.bounds.lanesPositive
    h.bounds.memoryMinimum pass lane slice index (s.gpr .rdi) h.bounds.laneBound
  have compressReady : FillCompress.Ready b := by
    apply compress_ready p b (h.layout.of_keeps keeps) h.bounds.lanesPositive
      lane (previousColumn p slice index) ref.1 ref.2 lane (currentColumn p slice index)
      h.bounds.laneBound previousBound refLane refColumn h.bounds.laneBound columnBound
    · rw [pointers.previous, matrixB]; rfl
    · rw [pointers.reference, matrixB]
    · rw [pointers.current, matrixB]; rfl
  exact ⟨compressReady, cur, prev, other, keeps⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

end


/-! Complete active-cell update from a random word and the matrix allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) (lane slice index : Nat) : List Region :=
  [⟨current s p lane slice index, 1024⟩, ⟨work s, 5120⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩]

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  block : blockAt t.mem (current s p lane slice index) =
    let next := Spec.Argon2.compress (blockAt s.mem (previous s p lane slice index))
      (blockAt s.mem (referenced s p pass lane slice index))
    if pass = 0 then next else xorBlock next (blockAt s.mem (current s p lane slice index))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p lane slice index) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.code s (Done s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.code
  refine WP.seq ((prepare_ok s p pass lane slice index h).mono ?_)
  intro b prepared
  have keeps := prepared.keeps
  have cur := prepared.currentPtr
  have prev := prepared.previousPtr
  have other := prepared.referencePtr
  refine (FillCompress.code_mx_ok b prepared.ready).mono ?_
  rintro t ⟨done, mx⟩
  have counter : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [keeps.mem, keeps.regs .rbp (by decide)]
    exact h.passWord
  refine ⟨?_, ?_, done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, mx.trans (ctl_eq_of keeps.mxcsr)⟩
  · have block := done.block
    rw [cur, prev, other, keeps.mem, counter] at block
    simp only [ReferenceMap.word_zero pass (Nat.lt_trans h.bounds.passBound (by decide))] at block
    exact block
  · intro r hr
    have ne : r ∉ ReferenceMap.changed := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (done.regs r hr).trans (keeps.regs r ne)
  · have workB : FillCompress.work b = work s := by
      unfold FillCompress.work work
      rw [keeps.regs .rbp (by decide), keeps.mem]
    have frame := done.frame
    rw [FillCompress.writes, workB, cur, keeps.regs .rsp (by decide), keeps.regs .rbp (by decide), keeps.mem] at frame
    change Frame [⟨current s p lane slice index, 1024⟩, ⟨work s + 4096, 1024⟩,
      ⟨work s, 4096⟩, below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩] s.mem t.mem at frame
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [writes], fun _ h => h⟩
    · exact ⟨⟨work s, 5120⟩, by simp [writes], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨work s, 5120⟩, by simp [writes], Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp [writes], fun _ h => h⟩
    · exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

end

/-! Merged from `Proof.Argon2.X86_64.FillKernelMatrix`. -/

@[expose] public section

section
/-! The filling step updates exactly one cell of the specification's block array. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def currentIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + currentColumn p slice index

def previousIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + previousColumn p slice index

def referenceIndex (s : State) (p : Params) (pass lane slice index : Nat) : Nat :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
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
    ready.bounds.memoryMinimum pass lane slice index (s.gpr .rdi) ready.bounds.laneBound
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

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Relate the complete assembly step to the reviewed filling-state transition. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem update_spec (s : State) (p : Params) (pass lane slice index : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (random : s.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    state.memory.set! (currentIndex p lane slice index) (nextBlock s p pass lane slice index state.memory) =
      (fillBlock p pass slice lane index state).memory := by
  rw [Proof.Argon2.FillStep.memory p pass lane slice index state active]
  unfold nextBlock referenceIndex
  rw [random]
  rfl

theorem code_spec_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory)
    (random : s.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    WP isa Impl.Argon2.X86_64.FillKernel.code s fun t => Done s t p pass lane slice index ∧
      Proof.Argon2.Represents t.mem (matrix s) p.blocks (fillBlock p pass slice lane index state).memory := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t done
  have represented' := done.represents ready state.memory represented
  rw [update_spec s p pass lane slice index state ready.bounds.active random] at represented'
  exact ⟨done, represented'⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

end

/-! Merged from `Proof.Argon2.X86_64.DependentWordPointer`. -/

@[expose] public section

section
/-! The data-dependent word's address is the specification's cyclic predecessor. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem args_ok (s : State) : WP isa (.block args) s fun t =>
    t.gpr .rcx = s.gpr .rdi ∧ t.gpr .rax = s.gpr .rbx ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa pointer s fun t =>
      t.gpr .rax = FillKernel.previous s p lane slice index ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold pointer
  refine WP.seq ((FillKernel.load_ok s .r8 232 (h.layout.frameRead 232 (by simp))).mono ?_)
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
  have lane' : c.gpr .rax = BitVec.ofNat 64 lane := laneReg.trans ((kb.regs .rbx (by decide)).trans pos.current)
  have length : c.gpr .r12 = BitVec.ofNat 64 p.laneLen :=
    (kc.regs .r12 (by decide)).trans ((kb.regs .r12 (by decide)).trans pos.laneLength)
  refine (BlockAddress.code_nat_ok c lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) p.laneLen lane' col' length).mono ?_
  rintro t ⟨address, kt⟩
  refine ⟨?_, ((k.trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [address, kc.regs .r8 (by decide), kb.regs .r8 (by decide), base]
  rfl

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Select the specified secret random word from the public previous-cell address. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem read_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax) 8) :
    WP isa (.block Impl.Argon2.X86_64.DependentWord.read) s fun t => t.gpr .rdi = s.mem.readW (s.gpr .rax) 64 ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.DependentWord.read, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, BitVec.add_zero, hr, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa code s fun t =>
      t.gpr .rdi = (blockAt s.mem (FillKernel.previous s p lane slice index))[0] ∧
      Divide.Keeps ReferenceMap.changed s t := by
  unfold code
  refine WP.seq ((pointer_ok s p pass lane slice index h).mono ?_)
  rintro a ⟨pointer, keeps⟩
  have bound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  have cover := h.layout.cell_cover h.bounds.lanesPositive h.bounds.laneBound bound
  have hr : InRegions (a.rd ++ a.wr) (a.gpr .rax) 8 := by
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
      t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
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

end VG.Proof.Argon2.X86_64.DependentWord
