import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
import VerifiedGarbage.Impl.Argon2.AArch64.FillIteration
import VerifiedGarbage.Impl.Argon2.AArch64.FillSlices
import VerifiedGarbage.Impl.Argon2.AArch64.FillSlice
import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Impl.Argon2.AArch64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock
import VerifiedGarbage.Impl.Argon2.AArch64.FillSegment
import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Impl.Argon2.AArch64.AddressMode
import VerifiedGarbage.Impl.Argon2.AArch64.DependentWord
import VerifiedGarbage.Proof.Argon2.AArch64.Compress
import VerifiedGarbage.Impl.Argon2.AArch64.FirstLane
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceStart

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderLit`. -/
section

/-! Checked literal of the independent-address input header. -/

namespace VG

materialize_code Impl.Argon2.AArch64.AddressHeader.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ClearBlockLit`. -/
section

/-! Checked literal of a complete address-generation block clear. -/

namespace VG

materialize_code Impl.Argon2.AArch64.ClearBlock.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillSegmentBody`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillIndex`. -/
section
/-! Public segment-index advancement retains the filling and cache allocations. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSegment

theorem advance_ok (s : State)
    (ha : (s.gpr .x23 + 1).toNat < 2 ^ 63) (hb : (s.gpr .x21).toNat < 2 ^ 63) :
    WP isa (.block VG.Impl.Argon2.AArch64.FillSegment.advance) s fun t =>
      t.gpr .x23 = s.gpr .x23 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x23 + 1).toNat < (s.gpr .x21).toNat)) ∧
      Divide.Keeps [.x23, .x12, .x14, .x15] s t := by
  simp only [VG.Impl.Argon2.AArch64.FillSegment.advance, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.addi_ok s .x23 1 (by decide) (by decide) (by decide)).mono ?_
  rintro a ⟨value, ka⟩
  have endEq := ka.regs .x21 (by decide)
  refine (Instructions.compare_ok a .x23 .x21 (by rw [value]; exact ha)
    (by rw [endEq]; exact hb)).mono ?_
  rintro t ⟨flag, kt⟩
  refine ⟨(kt.regs .x23 (by decide)).trans value, ?_, ?_⟩
  · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, value, endEq]
    cases decide ((s.gpr .x23 + 1).toNat < (s.gpr .x21).toNat) <;> rfl
  · exact (ka.mono (by decide)).trans (kt.mono (by decide))

theorem advance_nat_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa (.block VG.Impl.Argon2.AArch64.FillSegment.advance) s fun t =>
      t.gpr .x23 = BitVec.ofNat 64 (index + 1) ∧
      eval (.nonzero .x .x14) t = some (decide (index + 1 < p.segmentLen)) ∧ Divide.Keeps [.x23, .x12, .x14, .x15] s t := by
  have inputBound : (s.gpr .x23 + 1).toNat < 2 ^ 63 := by
    rw [h.position.index, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
      ReferenceMap.word_nat (index + 1) (by
        have := h.bounds.indexBound
        have := h.bounds.segment_le_lane
        have := h.bounds.laneLength_bound
        omega)]
    have := h.bounds.indexBound
    have := h.bounds.segment_le_lane
    have := h.bounds.laneLength_bound
    omega
  have endBound63 : (s.gpr .x21).toNat < 2 ^ 63 := by
    rw [h.position.segmentLength, ReferenceMap.word_nat p.segmentLen
      (Nat.lt_of_le_of_lt h.bounds.segment_le_lane
        (Nat.lt_trans h.bounds.laneLength_bound (by decide)))]
    have := h.bounds.segment_le_lane
    have := h.bounds.laneLength_bound
    omega
  refine (VG.Proof.Argon2.AArch64.FillSegment.advance_ok s inputBound endBound63).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : s.gpr .x23 + 1 = BitVec.ofNat 64 (index + 1) := by
    rw [h.position.index, BitVec.ofNat_add]; rfl
  have endBound : p.segmentLen < 2 ^ 64 := Nat.lt_of_le_of_lt h.bounds.segment_le_lane
    (Nat.lt_trans h.bounds.laneLength_bound (by decide))
  have indexBound := h.bounds.indexBound
  refine ⟨value.trans added, ?_, keeps⟩
  rw [flag, added, h.position.segmentLength,
    ReferenceMap.word_nat (index + 1) (by omega), ReferenceMap.word_nat p.segmentLen endBound]

theorem next_ready {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : RandomSource.Ready p pass lane slice index old s)
    (k : Divide.Keeps [.x23, .x12, .x14, .x15] s t) (value : t.gpr .x23 = BitVec.ofNat 64 (index + 1))
    (active : index + 1 < p.segmentLen) : RandomSource.Ready p pass lane slice (index + 1) old t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  have kernelWork : FillKernel.work t = FillKernel.work s := work
  refine ⟨?_, h.cache.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide)) k.sp k.mem k.rd k.wr, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · rw [k.rd, k.wr, bp]; exact h.filling.layout.frameRead
      · rw [k.wr, bp]; exact h.filling.layout.frameWrite
      · rw [base, k.wr]; exact h.filling.layout.matrixWrite
      · rw [kernelWork, k.wr]; exact h.filling.layout.workWrite
      · rw [base, kernelWork]; exact h.filling.layout.matrixWork
      · rw [base, bp]; exact h.filling.layout.matrixFrame
      · rw [base, sp]; exact h.filling.layout.matrixStack
      · rw [bp, kernelWork]; exact h.filling.layout.frameWork
      · rw [bp, sp]; exact h.filling.layout.frameStack
      · rw [sp, kernelWork]; exact h.filling.layout.stackWork
    · have bounds := h.filling.bounds
      refine ⟨bounds.lanesPositive, bounds.lanesBound, bounds.memoryMinimum, bounds.memoryBound,
        bounds.passBound, bounds.laneBound, bounds.sliceBound, active, ?_⟩
      rcases bounds.active with hp | hs | hi
      · exact Or.inl hp
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (by omega))
    · exact ⟨(k.regs .x24 (by decide)).trans h.filling.position.current,
        (k.regs .x20 (by decide)).trans h.filling.position.laneLength,
        (k.regs .x21 (by decide)).trans h.filling.position.segmentLength,
        (k.regs .x22 (by decide)).trans h.filling.position.slice, value⟩
    · rw [k.mem, bp]; exact h.filling.passWord
    · rw [k.mem, bp]; exact h.filling.lanesWord
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.AArch64.FillSegment
end

/-! Merged from `Proof.Argon2.AArch64.FillAllocation`. -/
section
/-! Transport the allocation using just its public pointers and permissions. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem Layout.of_preserved {p : Params} {s t : State} (h : Layout p s)
    (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : matrix t = matrix s) (scratch : work t = work s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Layout p t := by
  constructor
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [wr, bp]; exact h.frameWrite
  · rw [base, wr]; exact h.matrixWrite
  · rw [scratch, wr]; exact h.workWrite
  · rw [base, scratch]; exact h.matrixWork
  · rw [base, bp]; exact h.matrixFrame
  · rw [base, sp]; exact h.matrixStack
  · rw [bp, scratch]; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, scratch]; exact h.stackWork

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! One segment iteration updates the specified cell and advances its public index. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice (index + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  cf : eval (.nonzero .x .x14) t = some (decide (index + 1 < p.segmentLen))
  next : index + 1 < p.segmentLen → ∃ old, RandomSource.Ready p pass lane slice (index + 1) old t

theorem body_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSegment.body s (VG.Proof.Argon2.AArch64.FillSegment.Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.FillSegment.body
  refine WP.seq ((FillBlock.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a filled
  obtain ⟨counter, ready⟩ := filled.ready
  refine (VG.Proof.Argon2.AArch64.FillSegment.advance_nat_ok a p pass lane slice index ready.filling).mono ?_
  rintro t ⟨value, cf, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, ?_, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ?_, ?_, ?_, ?_, ?_, cf, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · exact ⟨(keeps.regs .x24 (by decide)).trans ready.filling.position.current,
      (keeps.regs .x20 (by decide)).trans ready.filling.position.laneLength,
      (keeps.regs .x21 (by decide)).trans ready.filling.position.segmentLength,
      (keeps.regs .x22 (by decide)).trans ready.filling.position.slice, value⟩
  · rw [keeps.mem]; exact filled.frame
  · intro r hr ne
    have outside : r ∉ [Reg.x23, .x12, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr)
  · exact ready.filling.layout.of_preserved bp (keeps.sp) base work keeps.rd keeps.wr
  · exact ⟨counter, ready.cache.of_state (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr⟩
  · rw [base, work]; exact ready.matrixWork
  · rw [keeps.mem, bp]; exact ready.filling.passWord
  · rw [keeps.mem, bp]; exact ready.filling.lanesWord
  · intro active; exact ⟨counter, VG.Proof.Argon2.AArch64.FillSegment.next_ready ready keeps value active⟩

end VG.Proof.Argon2.AArch64.FillSegment

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillSegment`. -/
section

/-! Termination and correctness of the active suffix of one segment. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice p.segmentLen t
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp

theorem Done.finished {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (h : VG.Proof.Argon2.AArch64.FillSegment.Done s t p pass lane slice index state) (last : index + 1 = p.segmentLen) :
    VG.Proof.Argon2.AArch64.FillSegment.Finished s t p pass lane slice (fillBlock p pass slice lane index state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.position, h.layout, h.cache,
    h.matrixWork, h.passWord, h.lanesWord, h.regs, h.rd, h.wr, h.frame, h.sp⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice index : Nat}
    {state finalState : FillState} (first : VG.Proof.Argon2.AArch64.FillSegment.Done s a p pass lane slice index state)
    (rest : VG.Proof.Argon2.AArch64.FillSegment.Finished a t p pass lane slice finalState) : VG.Proof.Argon2.AArch64.FillSegment.Finished s t p pass lane slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work,
    rest.position, rest.layout, rest.cache, rest.matrixWork, rest.passWord, rest.lanesWord,
    ?_, rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp⟩
  · intro r hr ne; exact (rest.regs r hr ne).trans (first.regs r hr ne)
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)] at frame
    exact first.frame.trans frame

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    WP isa Impl.Argon2.AArch64.FillSegment.loop s
      (VG.Proof.Argon2.AArch64.FillSegment.Finished s · p pass lane slice (Proof.Argon2.segment p pass lane slice index count state)) := by
  induction count generalizing s index old state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.AArch64.FillSegment.body_ok s p pass lane slice index old h state represented
    rw [Proof.Argon2.segment_succ]
    cases n with
    | zero =>
      have last : index + 1 = p.segmentLen := endIndex
      refine ⟨_, a, .loopExit run ?_, ?_⟩
      · simp only [done.cf, last, Nat.lt_irrefl, decide_false]
      · exact done.finished last
    | succ n =>
      have active : index + 1 < p.segmentLen := by omega
      obtain ⟨nextCounter, nextReady⟩ := done.next active
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (index + 1) nextCounter nextReady
        (fillBlock p pass slice lane index state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.FillSegment

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupSteps`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillContext`. -/
section
/-! A segment context allows its starting and final indices, including an empty suffix. -/

namespace VG.Proof.Argon2.AArch64.FillContext

open VG VG.AArch64 VG.Spec.Argon2

structure Parameters (p : Params) (pass lane slice : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  parameters : VG.Proof.Argon2.AArch64.FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  position : ReferenceMap.Position p lane slice index s
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.activate {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : VG.Proof.Argon2.AArch64.FillContext.Ready p pass lane slice index old s) (bound : index < p.segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) : RandomSource.Ready p pass lane slice index old s :=
  ⟨⟨h.layout, ⟨h.parameters.lanesPositive, h.parameters.lanesBound, h.parameters.memoryMinimum,
    h.parameters.memoryBound, h.parameters.passBound, h.parameters.laneBound, h.parameters.sliceBound,
    bound, active⟩, h.position, h.cache.words.passWord, h.lanesWord⟩, h.cache, h.matrixWork⟩

theorem Parameters.segment_bound {p : Params} {pass lane slice : Nat} (h : VG.Proof.Argon2.AArch64.FillContext.Parameters p pass lane slice) :
    2 ≤ p.segmentLen ∧ p.segmentLen < 2 ^ 64 := by
  have minimum := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have le : p.segmentLen ≤ p.blocks := by
    have blocks := Proof.Argon2.blocks_lanes p h.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
    have laneLe : p.laneLen ≤ p.blocks := by rw [blocks]; exact Nat.le_mul_of_pos_left _ h.lanesPositive
    omega
  exact ⟨minimum, Nat.lt_of_le_of_lt le
    (Nat.lt_trans (Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) h.memoryBound) (by decide))⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.FillContext.Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.AArch64.FillContext.Ready p pass lane slice index old t := by
  have bp := k.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp (k.sp) base work k.rd k.wr,
    h.cache.of_keeps k, ?_, h.position.of_keeps k, ?_⟩
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

theorem finished_context {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : VG.Proof.Argon2.AArch64.FillContext.Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    ∃ old, VG.Proof.Argon2.AArch64.FillContext.Ready p pass lane slice p.segmentLen old t := by
  obtain ⟨old, cache⟩ := h.cache
  exact ⟨old, parameters, h.layout, cache, h.matrixWork, h.position, h.lanesWord⟩

end VG.Proof.Argon2.AArch64.FillContext
end

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice := by
  unfold VG.Proof.Argon2.AArch64.SegmentSetup.start; split <;> omega

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice ≤ g := by
  unfold VG.Proof.Argon2.AArch64.SegmentSetup.start; split <;> omega

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block first) s fun t =>
      eval (.zero .x .x15) t = some (decide (s.mem.readW (off (s.gpr .x19) 0) 64 = 0#64 ∧ s.gpr .x22 = 0#64)) ∧
      Divide.Keeps [.x3, .x13, .x14, .x15] s t := by
  simp only [off, BitVec.add_zero] at hr
  apply WP.of_runBlock
  simp only [first, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.logic, Impl.Argon2.AArch64.Instructions.mark,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.comparei,
    Impl.Argon2.AArch64.Instructions.compare, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, hr, and_self,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    show (63 : Nat) < 64 from by decide, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    Bool.toNat_true, sub_value, show (0#16).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero, reduceCtorEq, ite_true, ite_false,
    eval, Bool.beq_eq_decide_eq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', off]
  refine ⟨?_, ?_⟩
  · congr 1
    exact propext BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : Nat) (bound : value < 65536) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm register value].flatten) s fun t =>
      t.gpr register = BitVec.ofNat 64 value ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.imm, bound, ite_true,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, Nat.reduceMul,
    Nat.reduceLT, BitVec.shiftLeft_zero, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (BitVec.ofNat 16 value).setWidth 64 = BitVec.ofNat 64 value
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) bound
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .x23 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) ∧ Divide.Keeps [.x3, .x23, .x13, .x14, .x15] s t := by
  unfold index
  refine WP.seq ((VG.Proof.Argon2.AArch64.SegmentSetup.first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : eval (.zero .x .x15) a = some (decide (pass = 0 ∧ slice = 0)) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) firstFlag ?_ ?_
  · intro mode
    refine (VG.Proof.Argon2.AArch64.SegmentSetup.register_ok a .x23 2 (by decide)).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold VG.Proof.Argon2.AArch64.SegmentSetup.start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (VG.Proof.Argon2.AArch64.SegmentSetup.register_ok a .x23 0 (by decide)).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold VG.Proof.Argon2.AArch64.SegmentSetup.start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State)
    (ha : (s.gpr .x23).toNat < 2 ^ 63) (hb : (s.gpr .x21).toNat < 2 ^ 63) :
    WP isa (.block check) s fun t =>
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x23).toNat < (s.gpr .x21).toNat)) ∧
      Divide.Keeps [.x14, .x15] s t := by
  simp only [check, List.flatten_cons, List.flatten_nil, List.append_nil]
  refine (Instructions.compare_ok s .x23 .x21 ha hb).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨?_, keeps⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, value]
  cases decide ((s.gpr .x23).toNat < (s.gpr .x21).toNat) <;> rfl

end VG.Proof.Argon2.AArch64.SegmentSetup

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare`. -/
section

/-! Merged from `Proof.Argon2.AArch64.SegmentSetupReset`. -/
section
/-! Merged from `Proof.Argon2.AArch64.SegmentSetupReady`. -/
section
/-! Segment setup needs no previously valid cached block. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.of_state {p : Params} {pass lane slice : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x24, .x20, .x21, .x22], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice t := by
  have bp := regs .x19 (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .x20 (by simp)).trans h.laneLength, (regs .x21 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, (regs .x24 (by simp)).trans words.laneWord,
      (regs .x22 (by simp)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem Ready.saved {p : Params} {pass lane slice : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s) (saved : AddressCache.Saved s t) : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice t := by
  have bp := congrFun saved.regs Reg.x19
  have sp := saved.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := saved.read 232 (by decide) (by decide)
  refine ⟨h.parameters, h.layout.of_preserved bp sp base saved.work_eq saved.rd saved.wr,
    saved.ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved.rd, saved.wr, bp]; exact h.reads
  · rw [saved.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    exact ⟨(s.gpr .x8).toNat, saved.words words (by simp)⟩
  · rw [base, saved.work_eq]; exact h.matrixWork
  · rw [saved.regs]; exact h.laneLength
  · rw [saved.regs]; exact h.segmentLength
  · exact (saved.read 184 (by decide) (by decide)).trans h.lanesWord

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! Reset the counter while preserving the segment header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Reset (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  ready : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice t
  words : AddressHeader.Words p pass lane slice 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem reset_ok (s : State) (p : Params) (pass lane slice : Nat) (h : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s) :
    WP isa VG.Impl.Argon2.AArch64.SegmentSetup.reset s (VG.Proof.Argon2.AArch64.SegmentSetup.Reset s · p pass lane slice) := by
  unfold VG.Impl.Argon2.AArch64.SegmentSetup.reset
  refine WP.seq ((VG.Proof.Argon2.AArch64.SegmentSetup.register_ok s .x8 0 (by decide)).mono ?_)
  rintro a ⟨value, keeps⟩
  have next := h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  refine (AddressCache.save_ready a next.addressLayout next.write).mono ?_
  intro t saved
  obtain ⟨old, words⟩ := next.words
  have matrixA : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have workA : AddressCalls.work a = AddressCalls.work s := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .x19 (by decide)]
  refine ⟨next.saved saved, saved.words words value,
    (saved.read 232 (by decide) (by decide)).trans matrixA, saved.work_eq.trans workA,
    ?_, saved.rd.trans keeps.rd, saved.wr.trans keeps.wr, ?_, saved.sp.trans keeps.sp⟩
  · intro r hr
    have ne : r ∉ [Reg.x8] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (congrFun saved.regs r).trans (keeps.regs r ne)
  · have frame := saved.frame
    rw [keeps.mem, keeps.regs .x19 (by decide)] at frame
    exact frame

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! The prepared context covers ordinary and empty first-segment suffixes. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Prepared (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  context : FillContext.Ready p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem prepare_ok (s : State) (p : Params) (pass lane slice : Nat) (h : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s) :
    WP isa VG.Impl.Argon2.AArch64.SegmentSetup.prepare s (VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s · p pass lane slice) := by
  unfold VG.Impl.Argon2.AArch64.SegmentSetup.prepare
  refine WP.seq ((VG.Proof.Argon2.AArch64.SegmentSetup.reset_ok s p pass lane slice h).mono ?_)
  intro a reset
  refine (VG.Proof.Argon2.AArch64.SegmentSetup.index_ok a pass slice (reset.ready.reads 0 (by simp)) reset.words.passWord reset.words.sliceWord
    (Nat.lt_trans h.parameters.passBound (by decide))
    (Nat.lt_trans h.parameters.sliceBound (by decide))).mono ?_
  rintro t ⟨value, keeps⟩
  have core := reset.ready.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  have cacheA : AddressCache.Invariant p pass lane slice 0 a :=
    ⟨reset.ready.addressLayout, reset.ready.reads, reset.ready.write, reset.words, by decide, Or.inl rfl⟩
  have cache := cacheA.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  have base : FillKernel.matrix t = FillKernel.matrix a := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have work : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .x19 (by decide)]
  refine ⟨⟨core.parameters, core.layout, cache, core.matrixWork,
    ⟨cache.words.laneWord, core.laneLength, core.segmentLength, cache.words.sliceWord, value⟩, core.lanesWord⟩,
    base.trans reset.matrix, work.trans reset.work, ?_, keeps.rd.trans reset.rd,
    keeps.wr.trans reset.wr, ?_, keeps.sp.trans reset.sp⟩
  · intro r hr ne
    have outside : r ∉ [Reg.x3, .x23, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reset.regs r hr)
  · rw [keeps.mem]; exact reset.frame

theorem Prepared.represents {p : Params} {pass lane slice : Nat} {s t : State}
    (ready : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s) (h : VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [h.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.SegmentSetup

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup`. -/
section

/-! Merged from `Proof.Argon2.AArch64.SegmentSetupCheck`. -/
section
/-! Check the prepared index before entering the nonempty segment loop. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

theorem Prepared.of_keeps {p : Params} {pass lane slice : Nat} {s a t : State}
    (h : VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s a p pass lane slice) (k : Divide.Keeps [.x14, .x15] a t) : VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s t p pass lane slice := by
  have bp := k.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.context.of_keeps (k.mono (by decide)), base.trans h.matrix, work.trans h.work,
    ?_, k.rd.trans h.rd, k.wr.trans h.wr, ?_, k.sp.trans h.sp⟩
  · intro r hr ne
    have outside : r ∉ [Reg.x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (k.regs r outside).trans (h.regs r hr ne)
  · rw [k.mem]; exact h.frame

theorem check_prepared_ok {p : Params} {pass lane slice : Nat} {s a : State}
    (h : VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s a p pass lane slice) : WP isa (.block check) a fun t =>
      VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s t p pass lane slice ∧ eval (.nonzero .x .x14) t = some (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen)) := by
  have segmentBound : p.segmentLen < 2 ^ 63 := by
    have laneLe : p.laneLen ≤ p.blocks := by
      rw [Proof.Argon2.blocks_lanes p h.context.parameters.lanesPositive]
      exact Nat.le_mul_of_pos_left _ h.context.parameters.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.context.parameters.lanesPositive
    have blocks := Proof.Argon2.blocks_le_memory p
    have memoryBound := h.context.parameters.memoryBound
    omega
  have minimum := h.context.parameters.segment_bound
  have startBound := Nat.lt_of_le_of_lt (VG.Proof.Argon2.AArch64.SegmentSetup.start_le pass slice p.segmentLen minimum.1) segmentBound
  refine (VG.Proof.Argon2.AArch64.SegmentSetup.check_ok a (by
    rw [h.context.position.index, ReferenceMap.word_nat _ (Nat.lt_trans startBound (by decide))]
    exact startBound) (by
    rw [h.context.position.segmentLength, ReferenceMap.word_nat _ minimum.2]
    exact segmentBound)).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨h.of_keeps keeps, ?_⟩
  rw [flag, h.context.position.index, h.context.position.segmentLength,
    ReferenceMap.word_nat (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) (Nat.lt_of_le_of_lt (VG.Proof.Argon2.AArch64.SegmentSetup.start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem finished_prepared {p : Params} {pass lane slice : Nat} {s a t : State} {state : FillState}
    (prepared : VG.Proof.Argon2.AArch64.SegmentSetup.Prepared s a p pass lane slice) (finished : FillSegment.Finished a t p pass lane slice state) :
    FillSegment.Finished s t p pass lane slice state := by
  refine ⟨finished.represented, finished.matrix.trans prepared.matrix, finished.work.trans prepared.work,
    finished.position, finished.layout, finished.cache, finished.matrixWork, finished.passWord, finished.lanesWord,
    ?_, finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.sp.trans prepared.sp⟩
  · intro r hr ne; exact (finished.regs r hr ne).trans (prepared.regs r hr ne)
  · have firstFrame : Frame (FillBlock.writes s p) s.mem a.mem := by
      apply prepared.frame.sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨off (s.gpr .x19) 8, 16⟩, by simp [FillBlock.writes], Region.sub_prefix (by decide)⟩
    have rest := finished.frame
    rw [FillBlock.writes, prepared.matrix, prepared.work,
      prepared.sp,
      prepared.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)] at rest
    exact firstFrame.trans rest

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! Fill one complete segment, including the initialized prefix and empty suffix. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

theorem code_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa VG.Impl.Argon2.AArch64.SegmentSetup.code s (FillSegment.Finished s · p pass lane slice
      (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state)) := by
  rw [Proof.Argon2.segment_start p pass lane slice state h.parameters.segment_bound.1]
  change WP isa VG.Impl.Argon2.AArch64.SegmentSetup.code s (FillSegment.Finished s · p pass lane slice
    (Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) state))
  unfold VG.Impl.Argon2.AArch64.SegmentSetup.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.SegmentSetup.prepare_ok s p pass lane slice h).mono ?_)
  intro a prepared
  refine WP.seq ((VG.Proof.Argon2.AArch64.SegmentSetup.check_prepared_ok prepared).mono ?_)
  rintro b ⟨prepared, flag⟩
  have matrix := prepared.represents h state.memory represented
  refine WP.ite (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen)) flag ?_ ?_
  · intro taken
    have bound := of_decide_eq_true taken
    have active := prepared.context.activate bound (VG.Proof.Argon2.AArch64.SegmentSetup.start_active pass slice)
    refine (FillSegment.loop_ok (p.segmentLen - VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) b p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0
      active state matrix (by omega) (by omega)).mono ?_
    intro t finished
    exact VG.Proof.Argon2.AArch64.SegmentSetup.finished_prepared prepared finished
  · intro skipped
    have bound := of_decide_eq_false skipped
    have minimum := h.parameters.segment_bound.1
    have last : VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice = p.segmentLen := by have := VG.Proof.Argon2.AArch64.SegmentSetup.start_le pass slice p.segmentLen minimum; omega
    have finished : FillSegment.Finished b b p pass lane slice state :=
      ⟨matrix, rfl, rfl, last ▸ prepared.context.position, prepared.context.layout,
        ⟨0, prepared.context.cache⟩, prepared.context.matrixWork, prepared.context.cache.words.passWord,
        prepared.context.lanesWord, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
    rw [last, Nat.sub_self, Proof.Argon2.segment_zero]
    exact WP.block_nil (VG.Proof.Argon2.AArch64.SegmentSetup.finished_prepared prepared finished)

end VG.Proof.Argon2.AArch64.SegmentSetup

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillLaneAdvance`. -/
section

/-! Lane advancement retains the allocation and public segment parameters. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillLanes

theorem advance_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8)
    (ha : (s.gpr .x24 + 1).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 184) 64).toNat < 2 ^ 63) :
    WP isa (.block VG.Impl.Argon2.AArch64.FillLanes.advance) s fun t => t.gpr .x24 = s.gpr .x24 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x24 + 1).toNat <
        (s.mem.readW (off (s.gpr .x19) 184) 64).toNat)) ∧
      Divide.Keeps [.x24, .x12, .x13, .x14, .x15] s t := by
  simp only [VG.Impl.Argon2.AArch64.FillLanes.advance, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.addi_ok s .x24 1 (by decide) (by decide) (by decide)).mono ?_
  rintro u ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have read : InRegions (u.rd ++ u.wr) (off (u.gpr .x19) 184) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact hr
  have left : (u.gpr .x24).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (u.mem.readW (off (u.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (Instructions.comparem_ok u .x24 .x19 184 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, changed⟩
  refine ⟨(changed.regs .x24 (by decide)).trans value, ?_,
    (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
  rw [flag, value, keeps.mem, bp]
  rfl

theorem context_ready {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : FillContext.Ready p pass lane slice index old s) : SegmentSetup.Ready p pass lane slice s :=
  ⟨h.parameters, h.layout, h.cache.layout, h.cache.reads, h.cache.write, ⟨old, h.cache.words⟩,
    h.matrixWork, h.position.laneLength, h.position.segmentLength, h.lanesWord⟩

theorem finished_ready {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : FillContext.Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    SegmentSetup.Ready p pass lane slice t := by
  obtain ⟨old, context⟩ := FillContext.finished_context parameters h
  exact VG.Proof.Argon2.AArch64.FillLanes.context_ready context

theorem change_lane_ready {p : Params} {pass lane slice newLane : Nat} {s t : State}
    (h : SegmentSetup.Ready p pass lane slice s) (k : Divide.Keeps [.x24, .x12, .x13, .x14, .x15] s t)
    (value : t.gpr .x24 = BitVec.ofNat 64 newLane) (active : newLane < p.lanes) :
    SegmentSetup.Ready p pass newLane slice t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨{ h.parameters with laneBound := active }, h.layout.of_preserved bp sp base work k.rd k.wr,
    ?_, ?_, ?_, ?_, ?_, (k.regs .x20 (by decide)).trans h.laneLength,
    (k.regs .x21 (by decide)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [k.rd, k.wr, bp]; exact h.addressLayout.frameRead
    · rw [k.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [k.rd, k.wr, bp]; exact h.reads
  · rw [k.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, value, (k.regs .x22 (by decide)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [k.mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

end VG.Proof.Argon2.AArch64.FillLanes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillLanesBody`. -/
section

/-! One lane iteration fills its segment and advances the public lane. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 (lane + 1)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x23 → t.gpr r = s.gpr r
  header : ∃ a, SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.x24, .x12, .x13, .x14, .x15] a t
  cf : eval (.nonzero .x .x14) t = some (decide (lane + 1 < p.lanes))
  next : lane + 1 < p.lanes → SegmentSetup.Ready p pass (lane + 1) slice t

theorem body_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillLanes.body s (VG.Proof.Argon2.AArch64.FillLanes.Done s · p pass lane slice state) := by
  unfold Impl.Argon2.AArch64.FillLanes.body
  refine WP.seq ((SegmentSetup.code_ok s p pass lane slice h state represented).mono ?_)
  intro a filled
  have ready := VG.Proof.Argon2.AArch64.FillLanes.finished_ready h.parameters filled
  obtain ⟨old, words⟩ := ready.words
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [words.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.parameters.laneBound
  have lanesBound32 := h.parameters.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [ready.lanesWord, ReferenceMap.word_nat p.lanes (by omega)]; omega
  refine (VG.Proof.Argon2.AArch64.FillLanes.advance_ok a (ready.layout.frameRead 184 (by simp)) left right).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have nextWord := value.trans added
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans h.parameters.lanesBound (by decide)
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextWord, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ⟨a, ready, keeps⟩, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx ix
    have outside : r ∉ [Reg.x24, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr ix)
  · rw [flag, added, ready.lanesWord, ReferenceMap.word_nat (lane + 1) (by omega),
      ReferenceMap.word_nat p.lanes lanesBound]
  · intro active; exact VG.Proof.Argon2.AArch64.FillLanes.change_lane_ready ready keeps nextWord active

end VG.Proof.Argon2.AArch64.FillLanes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillLanes`. -/
section

/-! Termination and correctness of all remaining lanes in one slice. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x23 → t.gpr r = s.gpr r
  header : ∃ lane a, lane + 1 = p.lanes ∧ SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.x24, .x12, .x13, .x14, .x15] a t

theorem Done.finished {s t : State} {p : Params} {pass lane slice : Nat} {state : FillState}
    (h : VG.Proof.Argon2.AArch64.FillLanes.Done s t p pass lane slice state) (last : lane + 1 = p.lanes) :
    VG.Proof.Argon2.AArch64.FillLanes.Finished s t p pass slice (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) := by
  obtain ⟨a, ready, keeps⟩ := h.header
  exact ⟨h.represented, h.matrix, h.work, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.sp,
    h.regs, lane, a, last, ready, keeps⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice : Nat} {state finalState : FillState}
    (first : VG.Proof.Argon2.AArch64.FillLanes.Done s a p pass lane slice state) (rest : VG.Proof.Argon2.AArch64.FillLanes.Finished a t p pass slice finalState) :
    VG.Proof.Argon2.AArch64.FillLanes.Finished s t p pass slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_, rest.header⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx ix; exact (rest.regs r hr bx ix).trans (first.regs r hr bx ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.AArch64.FillLanes.loop s
      (VG.Proof.Argon2.AArch64.FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice lane count state)) := by
  induction count generalizing s lane state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.AArch64.FillLanes.body_ok s p pass lane slice h state represented
    rw [Proof.Argon2.lanes_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.FillLanes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillSlice`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillSlicePrepare`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillHeader`. -/
section
/-! Allocation and normalized header across lane, slice and pass boundaries. -/

namespace VG.Proof.Argon2.AArch64.FillHeader

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem of_segment_ready {p : Params} {pass lane slice : Nat} {s : State}
    (h : SegmentSetup.Ready p pass lane slice s) : VG.Proof.Argon2.AArch64.FillHeader.Ready p pass lane slice s :=
  ⟨h.layout, h.addressLayout, h.reads, h.write, h.words, h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.segment {p : Params} {pass lane slice : Nat} {s : State}
    (h : VG.Proof.Argon2.AArch64.FillHeader.Ready p pass lane slice s) (parameters : FillContext.Parameters p pass lane slice) :
    SegmentSetup.Ready p pass lane slice s :=
  ⟨parameters, h.layout, h.addressLayout, h.reads, h.write, h.words,
    h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.of_state {p : Params} {pass lane slice newLane newSlice : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.FillHeader.Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x20, .x21], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (laneWord : t.gpr .x24 = BitVec.ofNat 64 newLane) (sliceWord : t.gpr .x22 = BitVec.ofNat 64 newSlice) :
    VG.Proof.Argon2.AArch64.FillHeader.Ready p pass newLane newSlice t := by
  have bp := regs .x19 (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .x20 (by simp)).trans h.laneLength, (regs .x21 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, laneWord, sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem of_lanes_finished {p : Params} {pass slice : Nat} {s t : State} {state : FillState}
    (h : FillLanes.Finished s t p pass slice state) : VG.Proof.Argon2.AArch64.FillHeader.Ready p pass p.lanes slice t := by
  obtain ⟨lane, a, _, ready, keeps⟩ := h.header
  obtain ⟨old, words⟩ := ready.words
  apply (VG.Proof.Argon2.AArch64.FillHeader.of_segment_ready ready).of_state _ keeps.sp keeps.mem keeps.rd keeps.wr h.laneWord
    ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)

end VG.Proof.Argon2.AArch64.FillHeader
end

/-! Initialize lane zero without requiring a valid incoming lane coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 slice
  header : ∃ lane, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass slice : Nat) : Prop where
  ready : SegmentSetup.Ready p pass 0 slice t
  keeps : Divide.Keeps [.x24] s t

theorem setup_ok (s : State) (p : Params) (pass slice : Nat) (h : VG.Proof.Argon2.AArch64.FillSlice.Ready p pass slice s) :
    WP isa (.block Impl.Argon2.AArch64.FillSlice.setup) s (VG.Proof.Argon2.AArch64.FillSlice.Prepared s · p pass slice) := by
  refine (SegmentSetup.register_ok s .x24 0 (by decide)).mono ?_
  rintro t ⟨laneWord, keeps⟩
  obtain ⟨lane, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass 0 slice t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr laneWord ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  exact ⟨next.segment h.parameters, keeps⟩

end VG.Proof.Argon2.AArch64.FillSlice
end

/-! Correctness of one complete slice, starting at lane zero. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass slice : Nat) (h : VG.Proof.Argon2.AArch64.FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlice.code s
      (FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice 0 p.lanes state)) := by
  unfold Impl.Argon2.AArch64.FillSlice.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillSlice.setup_ok s p pass slice h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillLanes.loop_ok p.lanes a p pass 0 slice prepared.ready state representedA
    h.parameters.lanesPositive (by omega)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.laneWord,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.sp.trans prepared.keeps.sp, ?_, finished.header⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.sp, bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx ix
    have ne : r ∉ [Reg.x24] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (finished.regs r hr bx ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.AArch64.FillSlice

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillSlicesBody`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillSliceAdvance`. -/
section
/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_ok (s : State) (ha : (s.gpr .x22 + 1).toNat < 2 ^ 63) :
    WP isa (.block VG.Impl.Argon2.AArch64.FillSlices.advance) s fun t => t.gpr .x22 = s.gpr .x22 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x22 + 1).toNat < 4)) ∧
      Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t := by
  simp only [VG.Impl.Argon2.AArch64.FillSlices.advance, List.flatten_cons, List.flatten_nil, List.append_nil,
    Impl.Argon2.AArch64.Instructions.comparei]
  apply WP.block_append
  refine (Instructions.addi_ok s .x22 1 (by decide) (by decide) (by decide)).mono ?_
  rintro a ⟨value, ka⟩
  apply WP.block_append
  refine (SegmentSetup.register_ok a .x13 4 (by decide)).mono ?_
  rintro b ⟨bound, kb⟩
  have left : (b.gpr .x22).toNat < 2 ^ 63 := by
    rw [kb.regs .x22 (by decide), value]; exact ha
  have right : (b.gpr .x13).toNat < 2 ^ 63 := by rw [bound]; decide
  refine (Instructions.compare_ok b .x22 .x13 left right).mono ?_
  rintro t ⟨flag, kt⟩
  have val := (kt.regs .x22 (by decide)).trans ((kb.regs .x22 (by decide)).trans value)
  refine ⟨val, ?_, (ka.mono (by decide)).trans
    ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag,
    kb.regs .x22 (by decide), value, bound, show (BitVec.ofNat 64 4).toNat = 4 from rfl]
  cases decide ((s.gpr .x22 + 1).toNat < 4) <;> rfl

theorem advanced_header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t)
    (value : t.gpr .x22 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.sp k.mem k.rd k.wr ((k.regs .x24 (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! Fill one slice and advance its public coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.lanes p pass slice 0 p.lanes state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes (slice + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (slice + 1 < 4))
  next : slice + 1 < 4 → FillSlice.Ready p pass (slice + 1) t

theorem body_ok (s : State) (p : Params) (pass slice : Nat) (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.body s (VG.Proof.Argon2.AArch64.FillSlices.Done s · p pass slice state) := by
  unfold Impl.Argon2.AArch64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  have sliceBound := h.parameters.sliceBound
  have added : a.gpr .x22 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have inputBound : (a.gpr .x22 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (slice + 1) (by omega)]; omega
  refine (VG.Proof.Argon2.AArch64.FillSlices.advance_ok a inputBound).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have nextWord := value.trans added
  have nextHeader := VG.Proof.Argon2.AArch64.FillSlices.advanced_header header keeps nextWord
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextHeader, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx sl ix
    have outside : r ∉ [Reg.x22, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr bx ix)
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega)]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.AArch64.FillSlices

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillSlices`. -/
section

/-! Termination and correctness of the four-slice filling pass. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass slice : Nat} {state : FillState}
    (h : VG.Proof.Argon2.AArch64.FillSlices.Done s t p pass slice state) (last : slice + 1 = 4) :
    VG.Proof.Argon2.AArch64.FillSlices.Finished s t p pass (Proof.Argon2.lanes p pass slice 0 p.lanes state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass slice : Nat} {state finalState : FillState}
    (first : VG.Proof.Argon2.AArch64.FillSlices.Done s a p pass slice state) (rest : VG.Proof.Argon2.AArch64.FillSlices.Finished a t p pass finalState) : VG.Proof.Argon2.AArch64.FillSlices.Finished s t p pass finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass slice : Nat)
    (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (VG.Proof.Argon2.AArch64.FillSlices.Finished s · p pass (Proof.Argon2.slices p pass slice count state)) := by
  induction count generalizing s slice state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.AArch64.FillSlices.body_ok s p pass slice h state represented
    rw [Proof.Argon2.slices_succ]
    cases n with
    | zero =>
      have last : slice + 1 = 4 := endSlice
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : slice + 1 < 4 := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (slice + 1) (done.next active)
        (Proof.Argon2.lanes p pass slice 0 p.lanes state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem pass_ok (s : State) (p : Params) (pass : Nat) (h : FillSlice.Ready p pass 0 s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (VG.Proof.Argon2.AArch64.FillSlices.Finished s · p pass (fillPass p state pass)) := by
  rw [← Proof.Argon2.slices_pass p pass state]
  exact VG.Proof.Argon2.AArch64.FillSlices.loop_ok 4 s p pass 0 h state represented (by decide) (by decide)

end VG.Proof.Argon2.AArch64.FillSlices

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillIteration`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillIterationPrepare`. -/
section
/-! Start a pass at slice zero regardless of its incoming lane and slice coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 0
  header : ∃ lane slice, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass : Nat) : Prop where
  ready : FillSlice.Ready p pass 0 t
  keeps : Divide.Keeps [.x22] s t

theorem setup_ok (s : State) (p : Params) (pass : Nat) (h : VG.Proof.Argon2.AArch64.FillIteration.Ready p pass s) :
    WP isa (.block Impl.Argon2.AArch64.FillIteration.setup) s (VG.Proof.Argon2.AArch64.FillIteration.Prepared s · p pass) := by
  refine (SegmentSetup.register_ok s .x22 0 (by decide)).mono ?_
  rintro t ⟨sliceWord, keeps⟩
  obtain ⟨lane, slice, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass lane 0 t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr ((keeps.regs .x24 (by decide)).trans words.laneWord) sliceWord
  exact ⟨⟨h.parameters, lane, next⟩, keeps⟩

end VG.Proof.Argon2.AArch64.FillIteration
end

/-! One complete filling pass against the reviewed specification. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass : Nat) (h : VG.Proof.Argon2.AArch64.FillIteration.Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.AArch64.FillIteration.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillIteration.setup_ok s p pass h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillSlices.pass_ok a p pass prepared.ready state representedA).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.header,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.sp.trans prepared.keeps.sp, ?_⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.sp, bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x22] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (finished.regs r hr bx sl ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.AArch64.FillIteration

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillIterationsBody`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FillPassSave`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillPassCounter`. -/
section
/-! Increment, save and compare the public pass counter. -/
namespace VG.Proof.Argon2.AArch64.FillIterations
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .x8 = s.mem.readW (off (s.gpr .x19) 0) 64 + 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  simp only [increment, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x8 .x19 0 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, ka⟩
  refine (Instructions.addi_ok a .x8 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [out, value]; rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.gpr .x8).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.gpr .x8) ∧
      (∀ r, r ∉ [Reg.x13, .x14, .x15] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
        (s.mem.readW (off (s.gpr .x19) 72) 64).toNat)) := by
  simp only [saveCheck, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.store_ok s .x19 .x8 0 (by decide) (by decide) hw).mono ?_
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have unchanged : a.mem.readW (off (a.gpr .x19) 72) 64 =
      s.mem.readW (off (s.gpr .x19) 72) 64 := by
    rw [regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by rw [regs, rd, wr]; exact hr
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [regs]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by rw [unchanged]; exact hb
  refine (Instructions.comparem_ok a .x8 .x19 72 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨keeps.mem.trans mem, ?_, keeps.rd.trans rd, keeps.wr.trans wr, keeps.sp.trans sp, ?_⟩
  · intro r hr; exact (keeps.regs r hr).trans (congrFun regs r)
  · change eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
      (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
    change eval (.nonzero .x .x14) t = some (decide ((a.gpr .x8).toNat <
      (a.mem.readW (off (a.gpr .x19) 72) 64).toNat)) at flag
    rw [flag, regs, mem]
    rw [Mem.readW_writeW_sep (w := 64) (w' := 64)
      (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! A saved pass counter changes only its eight-byte header word. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.mem.readW (off (s.gpr .x19) 0) 64 + 1)
  regs : ∀ r, r ∉ [Reg.x8, .x12, .x13, .x14, .x15] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cf : eval (.nonzero .x .x14) t = some (decide ((s.mem.readW (off (s.gpr .x19) 0) 64 + 1).toNat <
    (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
  frame : Frame [⟨off (s.gpr .x19) 0, 8⟩] s.mem t.mem

theorem advance_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (write : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (passesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.mem.readW (off (s.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) : WP isa VG.Impl.Argon2.AArch64.FillIterations.advance s (VG.Proof.Argon2.AArch64.FillIterations.Saved s) := by
  unfold VG.Impl.Argon2.AArch64.FillIterations.advance
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillIterations.increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have readA : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (off (a.gpr .x19) 0) 8 := by rw [keeps.wr, bp]; exact write
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (VG.Proof.Argon2.AArch64.FillIterations.saveCheck_ok a writeA readA left right).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx, cf⟩
  have finalMem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.mem.readW (off (s.gpr .x19) 0) 64 + 1) := by
    rw [mem, keeps.mem, bp, value]
  refine ⟨finalMem, ?_, rd.trans keeps.rd, wr.trans keeps.wr, mx.trans keeps.sp, ?_, ?_⟩
  · intro r ne
    have small : r ∉ [Reg.x8, .x12, .x15] := by
      intro hr; apply ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp_all
    have compare : r ∉ [Reg.x13, .x14, .x15] := by
      intro hr; apply ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp_all
    exact (regs r compare).trans (keeps.regs r small)
  · rw [cf, value, keeps.mem, bp]
  · rw [finalMem]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 0, 8⟩) (by simp) _ (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : VG.Proof.Argon2.AArch64.FillIterations.Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega) (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (h : VG.Proof.Argon2.AArch64.FillIterations.Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
    AddressHeader.Words p (pass + 1) lane slice old t := by
  refine ⟨?_, (h.regs .x24 (by decide)).trans words.laneWord,
    (h.regs .x22 (by decide)).trans words.sliceWord,
    (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord,
    (h.read 8 (by decide) (by decide)).trans words.counterWord⟩
  rw [h.regs .x19 (by decide), h.mem, Mem.readW_writeW_self64, words.passWord, BitVec.ofNat_add]
  rfl

theorem Saved.header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : VG.Proof.Argon2.AArch64.FillIterations.Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
  have bp := h.regs .x19 (by decide)
  have sp := h.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := h.read 248 (by decide) (by decide)
  refine ⟨header.layout.of_preserved bp sp base work h.rd h.wr, ?_, ?_, ?_, ?_, ?_,
    (h.regs .x20 (by decide)).trans header.laneLength, (h.regs .x21 (by decide)).trans header.segmentLength, ?_⟩
  · constructor
    · rw [h.rd, h.wr, bp]; exact header.addressLayout.frameRead
    · rw [h.wr, work]; exact header.addressLayout.workWrite
    · rw [bp, work]; exact header.addressLayout.frameWork
    · rw [bp, sp]; exact header.addressLayout.frameStack
    · rw [sp, work]; exact header.addressLayout.stackWork
  · rw [h.rd, h.wr, bp]; exact header.reads
  · rw [h.wr, bp]; exact header.write
  · obtain ⟨old, words⟩ := header.words; exact ⟨old, h.words words⟩
  · rw [base, work]; exact header.matrixWork
  · exact (h.read 184 (by decide) (by decide)).trans header.lanesWord

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! Merged from `Proof.Argon2.AArch64.FillIterationsFrame`. -/
section
/-! The outer pass loop also writes the public pass word at frame offset zero. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.sp) 8, ⟨s.gpr .x19, 24⟩]

theorem filling_frame {s t : State} {p : Params} (h : Frame (FillBlock.writes s p) s.mem t.mem) :
    Frame (VG.Proof.Argon2.AArch64.FillIterations.writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillIterations.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillIterations.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.FillIterations.writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x19, 24⟩, by simp [VG.Proof.Argon2.AArch64.FillIterations.writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.FillIterations.Saved s t) : Frame (VG.Proof.Argon2.AArch64.FillIterations.writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .x19, 24⟩, by simp [VG.Proof.Argon2.AArch64.FillIterations.writes], Offset.sub_base _ (by decide)⟩

theorem Saved.represents {s t : State} {p : Params} {pass lane slice : Nat}
    (h : VG.Proof.Argon2.AArch64.FillIterations.Saved s t) (header : FillHeader.Ready p pass lane slice s) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (header.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (off (s.gpr .x19) 0) 8

structure Done (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.FillIterations.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (pass + 1 < p.passes))
  next : pass + 1 < p.passes → VG.Proof.Argon2.AArch64.FillIterations.Ready p (pass + 1) t

theorem body_ok (s : State) (p : Params) (pass : Nat) (h : VG.Proof.Argon2.AArch64.FillIterations.Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIterations.body s (VG.Proof.Argon2.AArch64.FillIterations.Done s · p pass state) := by
  unfold Impl.Argon2.AArch64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (off (a.gpr .x19) 0) 8 := by
    rw [filled.wr, filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  obtain ⟨old, words⟩ := filled.header.words
  have passBound := h.filling.parameters.passBound
  have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
    rw [BitVec.ofNat_add]; rfl
  have left : (a.mem.readW (off (a.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63 := by
    rw [words.passWord, added, ReferenceMap.word_nat (pass + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [words.passesWord, ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
    exact Nat.lt_trans h.passesBound (by decide)
  refine (VG.Proof.Argon2.AArch64.FillIterations.advance_ok a (filled.header.reads 0 (by simp)) write
    (filled.header.reads 72 (by simp)) left right).mono ?_
  intro t saved
  have header := saved.header filled.header
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.sp.trans filled.sp, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [VG.Proof.Argon2.AArch64.FillIterations.writes, filled.matrix, filled.work,
      filled.sp,
      filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at lastFrame
    exact (VG.Proof.Argon2.AArch64.FillIterations.filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x8, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .x19 (by decide)]; exact write

end VG.Proof.Argon2.AArch64.FillIterations

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillIterations`. -/
section

/-! Termination and correctness of every requested filling pass. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p p.passes p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.FillIterations.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (h : VG.Proof.Argon2.AArch64.FillIterations.Done s t p pass state) (last : pass + 1 = p.passes) : VG.Proof.Argon2.AArch64.FillIterations.Finished s t p (fillPass p state pass) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass : Nat} {state finalState : FillState}
    (first : VG.Proof.Argon2.AArch64.FillIterations.Done s a p pass state) (rest : VG.Proof.Argon2.AArch64.FillIterations.Finished a t p finalState) : VG.Proof.Argon2.AArch64.FillIterations.Finished s t p finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [VG.Proof.Argon2.AArch64.FillIterations.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass : Nat) (h : VG.Proof.Argon2.AArch64.FillIterations.Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    WP isa Impl.Argon2.AArch64.FillIterations.loop s (VG.Proof.Argon2.AArch64.FillIterations.Finished s · p (Proof.Argon2.iterations p pass count state)) := by
  induction count generalizing s pass state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.AArch64.FillIterations.body_ok s p pass h state represented
    rw [Proof.Argon2.iterations_succ]
    cases n with
    | zero =>
      have last : pass + 1 = p.passes := endPass
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : pass + 1 < p.passes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (pass + 1) (done.next active)
        (fillPass p state pass) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem Finished.frame_word {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (ready : VG.Proof.Argon2.AArch64.FillIterations.Ready p pass s) (done : VG.Proof.Argon2.AArch64.FillIterations.Finished s t p state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : 24 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
  obtain ⟨lane, slice, header⟩ := ready.filling.header
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.AArch64.FillIterations.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact header.layout.matrixFrame.symm.sub_left sub
    · exact header.addressLayout.frameWork.sub_left sub
    · exact header.addressLayout.frameStack.sub_left sub
    · simpa only [off, BitVec.add_zero] using Offset.disjoint (d := d) (n := 8) (e := 0) (k := 24) (s.gpr .x19) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.FillIterations

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillPointersLit`. -/
section

/-! Checked literal of the complete filling pointer setup. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FillPointers.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupCT`. -/
section

/-! Merged from `Proof.Argon2.AArch64.SegmentSetupTrace`. -/
section
/-! Cache reset and initial-index selection branch only on public parameters. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure RelatedReady (p : Params) (pass lane slice : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s
  right : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem RelatedReady.of_keeps {p : Params} {pass lane slice : Nat} {s t a b : State}
    (h : VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice s t)
    (ka : Divide.Keeps [.x8, .x3, .x23, .x13, .x14, .x15] s a) (kb : Divide.Keeps [.x8, .x3, .x23, .x13, .x14, .x15] t b) :
    VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice a b := by
  have protectedRegs : ∀ r ∈ [Reg.x19, .x24, .x20, .x21, .x22], r ∉ [Reg.x8, .x3, .x23, .x13, .x14, .x15] := by decide
  refine ⟨h.left.of_state (fun r hr => ka.regs r (protectedRegs r hr)) ka.sp ka.mem ka.rd ka.wr,
    h.right.of_state (fun r hr => kb.regs r (protectedRegs r hr)) kb.sp kb.mem kb.rd kb.wr, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.work

theorem reset_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    VG.Impl.Argon2.AArch64.SegmentSetup.reset (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem reset_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice) VG.Impl.Argon2.AArch64.SegmentSetup.reset (VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice) := by
  have trace := reset_trace.mono (P' := VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.SegmentSetup.reset_ok s p pass lane slice h.left, VG.Proof.Argon2.AArch64.SegmentSetup.reset_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.ready, hb.ready, ?_, ?_, ha.matrix.trans (hp.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩
  · rw [ha.regs .x19 (by simp [FillCompress.loopRegs]), hb.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.bases
  · rw [ha.sp, hb.sp]; exact hp.stacks

theorem first_spec_ok (s : State) (p : Params) (pass lane slice : Nat) (h : VG.Proof.Argon2.AArch64.SegmentSetup.Ready p pass lane slice s) :
    WP isa (.block first) s fun t => eval (.zero .x .x15) t = some (decide (pass = 0 ∧ slice = 0)) ∧ Divide.Keeps [.x3, .x13, .x14, .x15] s t := by
  obtain ⟨old, words⟩ := h.words
  refine (VG.Proof.Argon2.AArch64.SegmentSetup.first_ok s (h.reads 0 (by simp))).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, words.passWord, words.sliceWord]
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 :=
    ReferenceMap.word_zero pass (Nat.lt_trans h.parameters.passBound (by decide))
  have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 :=
    ReferenceMap.word_zero slice (Nat.lt_trans h.parameters.sliceBound (by decide))
  simp only [passZero, sliceZero]

theorem first_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block first) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem first_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice) (.block first)
      (fun s t => VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t) := by
  have trace := first_trace.mono (P' := VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.SegmentSetup.first_spec_ok s p pass lane slice h.left, VG.Proof.Argon2.AArch64.SegmentSetup.first_spec_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps (ka.mono (by decide)) (kb.mono (by decide)), fa.trans fb.symm⟩

theorem index_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice) index (fun _ _ => True) := by
  have two : RelCT isa (fun s t : State => s.sp = t.sp)
      (.block [Impl.Argon2.AArch64.Instructions.imm .x23 2].flatten) (fun _ _ => True) :=
    (RelCT.taintRegs (τ := Taint.ofRegs [])
      (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
      [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have zero : RelCT isa (fun s t : State => s.sp = t.sp)
      (.block [Impl.Argon2.AArch64.Instructions.imm .x23 0].flatten) (fun _ _ => True) :=
    (RelCT.taintRegs (τ := Taint.ofRegs [])
      (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
      [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have branches : RelCT isa (fun s t => VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice s t ∧
      eval (.zero .x .x15) s = eval (.zero .x .x15) t)
      (.ite (.zero .x .x15)
        (.block [Impl.Argon2.AArch64.Instructions.imm .x23 2].flatten)
        (.block [Impl.Argon2.AArch64.Instructions.imm .x23 0].flatten)) (fun _ _ => True) :=
    RelCT.ite (by intro s t h; exact h.2)
      (two.mono (fun _ _ h => h.1.1.stacks) (fun _ _ h => h))
      (zero.mono (fun _ _ h => h.1.1.stacks) (fun _ _ h => h))
  exact (VG.Proof.Argon2.AArch64.SegmentSetup.first_public_rel p pass lane slice).seq branches

theorem prepare_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice) VG.Impl.Argon2.AArch64.SegmentSetup.prepare (fun _ _ => True) :=
  (VG.Proof.Argon2.AArch64.SegmentSetup.reset_public_rel p pass lane slice).seq (VG.Proof.Argon2.AArch64.SegmentSetup.index_trace p pass lane slice)

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceStartLit`. -/
section
/-! A checked literal for the chronological reference-window start. -/

namespace VG

materialize_code Impl.Argon2.AArch64.ReferenceStart.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceStartCT`. -/
section
/-! Branches depend only on the public position. -/
namespace VG.Proof.Argon2.AArch64.ReferenceStart
open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceStart

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x5, .x22, .x21], s.gpr r = t.gpr r) VG.Impl.Argon2.AArch64.ReferenceStart.code
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x6], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x22, .x21])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [.x6] (by taint_decide)
end VG.Proof.Argon2.AArch64.ReferenceStart
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapWindowCT`. -/
section
/-! The chronological window branches only on the public pass and slice. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

def PublicPosition (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x22, .x21], s.gpr r = t.gpr r

theorem window_rel : RelCT isa VG.Proof.Argon2.AArch64.ReferenceMap.PublicPosition window (fun s t => s.sp = t.sp) := by
  have start := ReferenceStart.code_rel.wpDep (fun s t _ =>
    ⟨ReferenceStart.code_ok s, ReferenceStart.code_ok t⟩)
  refine start.seq (ReferenceCount.code_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨eq.1, (ha.2.regs .x5 (by decide)).trans
    ((hp.2 .x5 (by simp)).trans (hb.2.regs .x5 (by decide)).symm)⟩

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapLaneCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FirstLaneLit`. -/
section
/-! A checked literal for the public first-slice lane override. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FirstLane.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.FirstLaneCT`. -/
section
/-! Branches depend only on the public position. -/
namespace VG.Proof.Argon2.AArch64.FirstLane
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FirstLane

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x5, .x22], s.gpr r = t.gpr r) VG.Impl.Argon2.AArch64.FirstLane.code
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x22])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)
end VG.Proof.Argon2.AArch64.FirstLane
end

/-! Recover the public pass from the frame without exposing the secret word. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

def Related (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s ∧ VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index t ∧ s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp

theorem division_keeps (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceLane.code s fun t =>
      VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t := by
  refine (ReferenceLane.code_ok s
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesPositive)
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesBound)).mono ?_
  rintro t ⟨_, _, keeps⟩
  have k : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .x1 (by decide)), k⟩

theorem division_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index)
      VG.Impl.Argon2.AArch64.ReferenceLane.code (VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index) := by
  have full := (ReferenceLane.code_secret_rel.mono
    (P' := VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index) (fun _ _ hp => hp.2.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨VG.Proof.Argon2.AArch64.ReferenceMap.division_keeps s p pass lane slice index hp.1,
        VG.Proof.Argon2.AArch64.ReferenceMap.division_keeps t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .x19 (by decide)).trans
    (hp.2.2.1.trans (hb.2.regs .x19 (by decide)).symm), eq⟩

theorem loadPass_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block loadPass) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

def Loaded (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index s t ∧
    s.gpr .x5 = BitVec.ofNat 64 pass ∧ t.gpr .x5 = BitVec.ofNat 64 pass

theorem loadPass_public (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index s) : WP isa (.block loadPass) s fun t =>
      VG.Proof.Argon2.AArch64.ReferenceMap.Ready p pass lane slice index t ∧ t.gpr .x5 = BitVec.ofNat 64 pass ∧
        Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t := by
  refine (loadPass_ok s ready.passRead).mono ?_
  rintro t ⟨loaded, keeps⟩
  have k : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .x1 (by decide)), loaded.trans ready.passWord, k⟩

theorem loadPass_public_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index) (.block loadPass)
      (VG.Proof.Argon2.AArch64.ReferenceMap.Loaded p pass lane slice index) := by
  have full := (loadPass_rel.mono (P' := VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨VG.Proof.Argon2.AArch64.ReferenceMap.loadPass_public s p pass lane slice index hp.1,
        VG.Proof.Argon2.AArch64.ReferenceMap.loadPass_public t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨⟨ha.1, hb.1, (ha.2.2.regs .x19 (by decide)).trans
    (hp.2.2.1.trans (hb.2.2.regs .x19 (by decide)).symm), eq⟩, ha.2.1, hb.2.1⟩

theorem firstLane_loaded_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReferenceMap.Loaded p pass lane slice index) VG.Impl.Argon2.AArch64.FirstLane.code
      (VG.Proof.Argon2.AArch64.ReferenceMap.Loaded p pass lane slice index) := by
  have trace := FirstLane.code_rel.mono (P' := VG.Proof.Argon2.AArch64.ReferenceMap.Loaded p pass lane slice index)
    (fun _ _ hp => ⟨hp.1.2.2.2, by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.2.1.trans hp.2.2.symm
      · exact hp.1.1.position.slice.trans hp.1.2.1.position.slice.symm⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t _ => ⟨FirstLane.code_ok s, FirstLane.code_ok t⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  have ka : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed s a := ha.2.mono (by decide)
  have kb : Divide.Keeps VG.Proof.Argon2.AArch64.ReferenceMap.changed t b := hb.2.mono (by decide)
  refine ⟨⟨hp.1.1.of_keeps ka (ha.2.regs .x1 (by decide)),
    hp.1.2.1.of_keeps kb (hb.2.regs .x1 (by decide)),
    (ka.regs .x19 (by decide)).trans (hp.1.2.2.1.trans (kb.regs .x19 (by decide)).symm), eq.1⟩, ?_, ?_⟩
  · exact (ha.2.regs .x5 (by decide)).trans hp.2.1
  · exact (hb.2.regs .x5 (by decide)).trans hp.2.2

theorem laneArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block laneArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepareLanes_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index) prepareLanes VG.Proof.Argon2.AArch64.ReferenceMap.PublicPosition := by
  have head := (VG.Proof.Argon2.AArch64.ReferenceMap.division_rel p pass lane slice index).seq
    ((VG.Proof.Argon2.AArch64.ReferenceMap.loadPass_public_rel p pass lane slice index).seq (VG.Proof.Argon2.AArch64.ReferenceMap.firstLane_loaded_rel p pass lane slice index))
  have trace := head.seq (laneArgs_secret_rel.mono (fun _ _ hp => hp.1.2.2.2) (fun _ _ h => h))
  have full := trace.wpDep (fun s t hp =>
    ⟨prepareLanes_ok s p pass lane slice index hp.1,
      prepareLanes_ok t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, _, _, _, ha, hb⟩ := h
  refine ⟨eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact ha.pass.trans hb.pass.symm
  · exact ha.position.slice.trans hb.position.slice.symm
  · exact ha.position.segmentLength.trans hb.position.segmentLength.symm

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapCT`. -/
section
/-! Complete reference mapping has no secret-dependent execution trace. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem relativeArgs_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.block relativeArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem wrapArgs_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.block wrapArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem tail_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.seq relative VG.Impl.Argon2.AArch64.ReferenceMap.finish) (fun s t => s.sp = t.sp) :=
  (relativeArgs_secret_rel.seq Relative.code_secret_rel).seq
    (wrapArgs_secret_rel.seq Wrap.code_secret_rel)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReferenceMap.Related p pass lane slice index) VG.Impl.Argon2.AArch64.ReferenceMap.code (fun s t => s.sp = t.sp) :=
  (VG.Proof.Argon2.AArch64.ReferenceMap.prepareLanes_rel p pass lane slice index).seq (window_rel.seq VG.Proof.Argon2.AArch64.ReferenceMap.tail_secret_rel)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.RandomSourceCounter`. -/
section
/-! The stored address counter remains public after either source. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

def counterValue (p : Params) (pass slice index old : Nat) : Addr :=
  BitVec.ofNat 64 (if independent p pass slice then index / 128 + 1 else old)

theorem counter_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s) :
    WP isa Impl.Argon2.AArch64.RandomSource.code s fun t =>
      t.mem.readW (off (t.gpr .x19) 8) 64 = VG.Proof.Argon2.AArch64.RandomSource.counterValue p pass slice index old := by
  unfold Impl.Argon2.AArch64.RandomSource.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.RandomSource.prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  refine WP.ite (!independent p pass slice) flag ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by cases eq : independent p pass slice <;> simp_all
    refine (DependentWord.code_ok a p pass lane slice index next.filling).mono ?_
    rintro t ⟨_, saved⟩
    unfold VG.Proof.Argon2.AArch64.RandomSource.counterValue
    simp only [dependent]
    rw [saved.mem, saved.regs .x19 (by decide)]
    exact next.cache.words.counterWord
  · intro mode
    have independent : independent p pass slice = true := by cases eq : independent p pass slice <;> simp_all
    refine (AddressCache.code_ok p pass lane slice old a next.cache.ready).mono ?_
    intro t done
    unfold VG.Proof.Argon2.AArch64.RandomSource.counterValue
    simp only [independent, ite_true]
    rw [done.selected.counterWord, AddressCache.counter_nat, next.index_nat]

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillCompressCallCT`. -/
section
/-! Compression calls reveal only their argument addresses and stack pointer. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64

theorem call_rel (name : String) {P : State → State → Prop}
    (pre : ∀ s t, P s t → VG.Proof.Argon2.AArch64.FillCompress.CallReady s ∧ VG.Proof.Argon2.AArch64.FillCompress.CallReady t ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
      s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp) :
    RelCT isa P (.call name Impl.Argon2.AArch64.compress) (fun _ _ => True) := by
  apply RelCT.callEx (k := compressLocal) VG.Proof.Argon2.AArch64.compress_correct compress_ct
  intro s t hp
  obtain ⟨hs, ht, di, si, dx, cx, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := call_hyps s hs
  obtain ⟨pt, ct, wt⟩ := call_hyps t ht
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧ s.sp = t.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs)]
  exact ⟨di, si, dx, cx, sp⟩

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Merged from `Proof.Argon2.AArch64.RandomSourceCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DependentWordLit`. -/
section
namespace VG.Impl.Argon2.AArch64.DependentWord
materialize_code pointer
end VG.Impl.Argon2.AArch64.DependentWord
end

/-! Merged from `Proof.Argon2.AArch64.DependentWordCT`. -/
section
/-! The previous cell is read at an address determined by public parameters. -/
namespace VG.Proof.Argon2.AArch64.DependentWord
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : FillKernel.Ready p pass lane slice index s
  right : FillKernel.Ready p pass lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t

theorem pointer_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    pointer (fun s t => s.sp = t.sp) := by
  have trace := RelCT.taintRegs (c := pointer) (τ := Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
    (P := fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)
  exact trace.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem read_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8)
    (.block Impl.Argon2.AArch64.DependentWord.read) (fun s t => s.sp = t.sp) := by
  have trace := RelCT.taintRegs (c := .block Impl.Argon2.AArch64.DependentWord.read)
    (τ := Taint.ofRegs [.x8]) (P := fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8)
    (fun _ _ h => ⟨h.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r; exact h.2⟩) [] (by taint_decide)
  exact trace.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.DependentWord.Related p pass lane slice index) VG.Impl.Argon2.AArch64.DependentWord.code (fun s t => s.sp = t.sp) := by
  have trace := pointer_rel.mono (P' := VG.Proof.Argon2.AArch64.DependentWord.Related p pass lane slice index) (by
    intro s t h
    refine ⟨h.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.bases
    · exact h.left.position.laneLength.trans h.right.position.laneLength.symm
    · exact h.left.position.segmentLength.trans h.right.position.segmentLength.symm
    · exact h.left.position.slice.trans h.right.position.slice.symm
    · exact h.left.position.index.trans h.right.position.index.symm) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨pointer_ok s p pass lane slice index h.left, pointer_ok t p pass lane slice index h.right⟩)
  have publicTrace : RelCT isa (VG.Proof.Argon2.AArch64.DependentWord.Related p pass lane slice index) pointer
      (fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨sp, s, t, hp, ⟨pa, _⟩, ⟨pb, _⟩⟩ := h
    have equal : FillKernel.previous s p lane slice index = FillKernel.previous t p lane slice index := by
      unfold FillKernel.previous; rw [hp.matrices]
    exact ⟨sp, pa.trans (equal.trans pb.symm)⟩)
  exact publicTrace.seq VG.Proof.Argon2.AArch64.DependentWord.read_rel

end VG.Proof.Argon2.AArch64.DependentWord
end

/-! Merged from `Proof.Argon2.AArch64.AddressModeLit`. -/
section
/-! Checked literal of the segment addressing-mode computation. -/

namespace VG

materialize_code Impl.Argon2.AArch64.AddressMode.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.AddressModeCT`. -/
section
/-! Mode selection has a fixed trace at the public frame base. -/
namespace VG.Proof.Argon2.AArch64.AddressMode
open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    VG.Impl.Argon2.AArch64.AddressMode.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.AddressMode
end

/-! Merged from `Proof.Argon2.AArch64.AddressInputCT`. -/
section
/-! Clearing and header preparation visit fixed offsets of public pointers. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64

theorem ClearBlock.code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0)
    Impl.Argon2.AArch64.ClearBlock.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.2⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem AddressHeader.code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x19], s.gpr r = t.gpr r)
    Impl.Argon2.AArch64.AddressHeader.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x19])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64
end

/-! Merged from `Proof.Argon2.AArch64.AddressGenerationCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.AddressCallsCT`. -/
section
/-! The two address-generation compression calls have public fixed addresses. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls

structure Related (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.AddressCalls.Ready s
  right : VG.Proof.Argon2.AArch64.AddressCalls.Ready t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  work : work s = work t

structure CallRelated (s t : State) : Prop where
  left : FillCompress.CallReady s
  right : FillCompress.CallReady t
  stacks : s.sp = t.sp
  args : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], s.gpr r = t.gpr r

theorem first_args_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (VG.Impl.Argon2.AArch64.AddressCalls.args 7168 5120 4096)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem second_args_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (VG.Impl.Argon2.AArch64.AddressCalls.args 7168 4096 6144)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem args_public_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (VG.Impl.Argon2.AArch64.AddressCalls.args x y out)) (fun s t => s.sp = t.sp)) :
    RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.Related (.block (VG.Impl.Argon2.AArch64.AddressCalls.args x y out)) VG.Proof.Argon2.AArch64.AddressCalls.CallRelated := by
  have trace := argTrace.mono (P' := VG.Proof.Argon2.AArch64.AddressCalls.Related) (fun _ _ hp => ⟨hp.bases, hp.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨args_nat_ok s hp.left x y out (by omega) (by omega) (by omega),
      args_nat_ok t hp.right x y out (by omega) (by omega) (by omega)⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨args_call_ready s a hp.left x y out hx hy ho bx by_ bo ha,
    args_call_ready t b hp.right x y out hx hy ho bx by_ bo hb, eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha.left.trans ((congrArg (fun p => off p x) hp.work).trans hb.left.symm)
  · exact ha.right.trans ((congrArg (fun p => off p y) hp.work).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (fun p => off p out) hp.work).trans hb.output.symm)
  · exact ha.scratch.trans (hp.work.trans hb.scratch.symm)

theorem stage_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (VG.Impl.Argon2.AArch64.AddressCalls.args x y out)) (fun s t => s.sp = t.sp)) :
    RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.Related (stage x y out) VG.Proof.Argon2.AArch64.AddressCalls.Related := by
  have call := FillCompress.call_rel Spec.Argon2.compressApi.name (P := VG.Proof.Argon2.AArch64.AddressCalls.CallRelated)
    (fun _ _ hp => ⟨hp.left, hp.right, hp.args .x0 (by simp), hp.args .x1 (by simp),
      hp.args .x2 (by simp), hp.args .x3 (by simp), hp.stacks⟩)
  have trace := (VG.Proof.Argon2.AArch64.AddressCalls.args_public_rel x y out hx hy ho bx by_ bo argTrace).seq call
  have full := trace.wpDep (fun s t hp =>
    ⟨stage_ok s hp.left x y out hx hy ho bx by_ bo,
      stage_ok t hp.right x y out hx hy ho bx by_ bo⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready, hb.ready,
    (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm),
    ha.sp.trans (hp.stacks.trans hb.sp.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩

theorem calls_rel : RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.Related calls VG.Proof.Argon2.AArch64.AddressCalls.Related :=
  (VG.Proof.Argon2.AArch64.AddressCalls.stage_rel 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) VG.Proof.Argon2.AArch64.AddressCalls.first_args_rel).seq
  (VG.Proof.Argon2.AArch64.AddressCalls.stage_rel 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) VG.Proof.Argon2.AArch64.AddressCalls.second_args_rel)

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Independent-address generation keeps its entire trace independent of secrets. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls

theorem Related.of_stable {s t a b : State} (h : VG.Proof.Argon2.AArch64.AddressCalls.Related s t)
    (ha : VG.Proof.Argon2.AArch64.AddressCalls.Stable s a) (hb : VG.Proof.Argon2.AArch64.AddressCalls.Stable t b) : VG.Proof.Argon2.AArch64.AddressCalls.Related a b :=
  ⟨ha.ready, hb.ready,
    (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (h.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm),
    ha.sp.trans (h.stacks.trans hb.sp.symm),
    ha.work_eq.trans (h.work.trans hb.work_eq.symm)⟩

theorem input_pointer_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (pointer 5120)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem zero_pointer_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (pointer 7168)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

structure PointRelated (s t : State) : Prop where
  related : VG.Proof.Argon2.AArch64.AddressCalls.Related s t
  pointer : s.gpr .x0 = t.gpr .x0

theorem pointer_public_rel (offset : Nat) (bound : offset ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (pointer offset)) (fun s t => s.sp = t.sp)) :
    RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.Related (.block (pointer offset)) VG.Proof.Argon2.AArch64.AddressCalls.PointRelated := by
  have publicTrace := trace.mono (P' := VG.Proof.Argon2.AArch64.AddressCalls.Related) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := publicTrace.wpDep (fun s t h =>
    ⟨pointer_ok s offset bound h.left.frameRead, pointer_ok t offset bound h.right.frameRead⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨pa, ka⟩, ⟨pb, kb⟩⟩ := h
  exact ⟨hp.of_stable (pointer_stable hp.left ka) (pointer_stable hp.right kb),
    pa.trans ((congrArg (· + BitVec.ofNat 64 offset) hp.work).trans pb.symm)⟩

theorem clearAt_rel (offset : Nat) (bound : offset + 1024 ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (pointer offset)) (fun s t => s.sp = t.sp)) :
    RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.Related (clearAt offset) VG.Proof.Argon2.AArch64.AddressCalls.Related := by
  have clear := ClearBlock.code_rel.mono (P' := VG.Proof.Argon2.AArch64.AddressCalls.PointRelated)
    (fun _ _ h => ⟨h.related.stacks, h.pointer⟩) (fun _ _ h => h)
  have blocks := (VG.Proof.Argon2.AArch64.AddressCalls.pointer_public_rel offset (by omega) trace).seq clear
  have full := blocks.wpDep (fun s t h =>
    ⟨clearAt_ok s h.left offset bound, clearAt_ok t h.right offset bound⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.of_stable (ha.stable bound) (hb.stable bound)

structure PrepareRelated (s t : State) : Prop where
  related : VG.Proof.Argon2.AArch64.AddressCalls.Related s t
  leftReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  rightReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8

theorem prepare_rel : RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.PrepareRelated VG.Impl.Argon2.AArch64.AddressCalls.prepare VG.Proof.Argon2.AArch64.AddressCalls.Related := by
  have header := AddressHeader.code_rel.mono (P' := VG.Proof.Argon2.AArch64.AddressCalls.PointRelated) (by
    intro s t h
    refine ⟨h.related.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.related.bases) (fun _ _ h => h)
  have trace := (VG.Proof.Argon2.AArch64.AddressCalls.clearAt_rel 5120 (by decide) VG.Proof.Argon2.AArch64.AddressCalls.input_pointer_rel).seq
    ((VG.Proof.Argon2.AArch64.AddressCalls.clearAt_rel 7168 (by decide) VG.Proof.Argon2.AArch64.AddressCalls.zero_pointer_rel).seq
      ((VG.Proof.Argon2.AArch64.AddressCalls.pointer_public_rel 5120 (by decide) VG.Proof.Argon2.AArch64.AddressCalls.input_pointer_rel).seq header))
  have narrowed := trace.mono (P' := VG.Proof.Argon2.AArch64.AddressCalls.PrepareRelated) (fun _ _ h => h.related) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_layout_ok s h.related.left h.leftReads,
      prepare_layout_ok t h.related.right h.rightReads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.related.of_stable ha.stable hb.stable

theorem code_rel : RelCT isa VG.Proof.Argon2.AArch64.AddressCalls.PrepareRelated VG.Impl.Argon2.AArch64.AddressCalls.code VG.Proof.Argon2.AArch64.AddressCalls.Related := prepare_rel.seq VG.Proof.Argon2.AArch64.AddressCalls.calls_rel

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheWordCT`. -/
section
/-! The cached random word is secret; its read address is public. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache

structure WordRelated (s t : State) : Prop where
  layout : AddressCalls.Related s t
  indices : s.gpr .x23 = t.gpr .x23

theorem wordArgs_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x23], s.gpr r = t.gpr r)
    (.block wordArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem wordRead_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x3, .x8], s.gpr r = t.gpr r)
    (.block wordRead) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x3, .x8])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem word_rel : RelCT isa VG.Proof.Argon2.AArch64.AddressCache.WordRelated Impl.Argon2.AArch64.AddressCache.word (fun s t => s.sp = t.sp) := by
  have trace := wordArgs_rel.mono (P' := VG.Proof.Argon2.AArch64.AddressCache.WordRelated) (by
    intro s t h
    refine ⟨h.layout.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.layout.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨wordArgs_ok s h.layout.left.frameRead, wordArgs_ok t h.layout.right.frameRead⟩)
  have args : RelCT isa VG.Proof.Argon2.AArch64.AddressCache.WordRelated (.block wordArgs)
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x3, .x8], s.gpr r = t.gpr r) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨eq, s, t, hp, ⟨sa, ia, _⟩, ⟨sb, ib, _⟩⟩ := h
    refine ⟨eq, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sa.trans (hp.layout.work.trans sb.symm)
    · exact ia.trans ((congrArg (· &&& 127) hp.indices).trans ib.symm))
  exact args.seq VG.Proof.Argon2.AArch64.AddressCache.wordRead_rel

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheSelectCT`. -/
section
/-! Cache regeneration branches only on public counters. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache

structure CacheRelated (s t : State) : Prop where
  prepare : AddressCalls.PrepareRelated s t
  indices : s.gpr .x23 = t.gpr .x23
  counters : s.mem.readW (off (s.gpr .x19) 8) 64 = t.mem.readW (off (t.gpr .x19) 8) 64
  leftWrite : InRegions s.wr (off (s.gpr .x19) 8) 8
  rightWrite : InRegions t.wr (off (t.gpr .x19) 8) 8

structure CheckedRelated (s t : State) : Prop where
  related : VG.Proof.Argon2.AArch64.AddressCache.CacheRelated s t
  values : s.gpr .x8 = t.gpr .x8
  flags : s.gpr .x15 = t.gpr .x15

theorem check_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x23], s.gpr r = t.gpr r)
    (.block check) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem check_public_rel : RelCT isa VG.Proof.Argon2.AArch64.AddressCache.CacheRelated (.block check) VG.Proof.Argon2.AArch64.AddressCache.CheckedRelated := by
  have trace := check_rel.mono (P' := VG.Proof.Argon2.AArch64.AddressCache.CacheRelated) (by
    intro s t h
    refine ⟨h.prepare.related.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.prepare.related.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.AArch64.AddressCache.check_ok s (h.prepare.leftReads 8 (by simp)), VG.Proof.Argon2.AArch64.AddressCache.check_ok t (h.prepare.rightReads 8 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨va, fa, ka⟩, ⟨vb, fb, kb⟩⟩ := h
  have sa := check_stable hp.prepare.related.left ka
  have sb := check_stable hp.prepare.related.right kb
  have index : a.gpr .x23 = b.gpr .x23 := (sa.regs .x23 (by simp [FillCompress.loopRegs])).trans
    (hp.indices.trans (sb.regs .x23 (by simp [FillCompress.loopRegs])).symm)
  have counters : a.mem.readW (off (a.gpr .x19) 8) 64 = b.mem.readW (off (b.gpr .x19) 8) 64 := by
    rw [ka.mem, kb.mem, sa.regs .x19 (by simp [FillCompress.loopRegs]), sb.regs .x19 (by simp [FillCompress.loopRegs])]
    exact hp.counters
  refine ⟨⟨⟨hp.prepare.related.of_stable sa sb, sa.reads hp.prepare.leftReads,
    sb.reads hp.prepare.rightReads⟩, index, counters, ?_, ?_⟩, ?_, ?_⟩
  · rw [ka.wr, sa.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.leftWrite
  · rw [kb.wr, sb.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.rightWrite
  · rw [va, vb, hp.indices]
  · rw [fa, fb, hp.indices, hp.counters]

theorem save_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block VG.Impl.Argon2.AArch64.AddressCache.save) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem save_public_rel : RelCT isa VG.Proof.Argon2.AArch64.AddressCache.CheckedRelated (.block VG.Impl.Argon2.AArch64.AddressCache.save) AddressCalls.PrepareRelated := by
  have trace := save_rel.mono (P' := VG.Proof.Argon2.AArch64.AddressCache.CheckedRelated)
    (fun _ _ h => ⟨h.related.prepare.related.bases, h.related.prepare.related.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨save_ready s h.related.prepare.related.left h.related.leftWrite,
      save_ready t h.related.prepare.related.right h.related.rightWrite⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ha.work_eq.trans
    (hp.related.prepare.related.work.trans hb.work_eq.symm)⟩, ?_, ?_⟩
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.bases
  · exact ha.sp.trans (hp.related.prepare.related.stacks.trans hb.sp.symm)
  · rw [ha.rd, ha.wr, ha.regs]; exact hp.related.prepare.leftReads
  · rw [hb.rd, hb.wr, hb.regs]; exact hp.related.prepare.rightReads

theorem select_trace : RelCT isa VG.Proof.Argon2.AArch64.AddressCache.CacheRelated select (fun _ _ => True) := by
  have noop : RelCT isa (fun s t : State => s.sp = t.sp) (.block []) (fun _ _ => True) :=
    RelCT.taint (A := VG.AArch64.taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) (by taint_decide)
  have branches : RelCT isa VG.Proof.Argon2.AArch64.AddressCache.CheckedRelated
      (.ite (.zero .x .x15) (.block []) (.seq (.block VG.Impl.Argon2.AArch64.AddressCache.save) Impl.Argon2.AArch64.AddressCalls.code))
      (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, State.read, h.flags])
      (noop.mono (fun _ _ h => h.1.related.prepare.related.stacks) (fun _ _ h => h))
      ((save_public_rel.seq AddressCalls.code_rel).mono (fun _ _ h => h.1) (fun _ _ _ => trivial))
  exact check_public_rel.seq branches

structure ReadyRelated (p : Spec.Argon2.Params) (pass lane slice old : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old s
  right : VG.Proof.Argon2.AArch64.AddressCache.Ready p pass lane slice old t
  pubs : VG.Proof.Argon2.AArch64.AddressCache.CacheRelated s t

theorem select_public_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.AddressCache.ReadyRelated p pass lane slice old) select VG.Proof.Argon2.AArch64.AddressCache.WordRelated := by
  have trace := select_trace.mono (P' := VG.Proof.Argon2.AArch64.AddressCache.ReadyRelated p pass lane slice old)
    (fun _ _ h => h.pubs) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨selected_ok p pass lane slice old s h.left, selected_ok p pass lane slice old t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.layout, hb.layout, ?_, ?_, ha.work_eq.trans
    (hp.pubs.prepare.related.work.trans hb.work_eq.symm)⟩, ?_⟩
  · exact (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.pubs.prepare.related.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm)
  · exact ha.sp.trans (hp.pubs.prepare.related.stacks.trans hb.sp.symm)
  · exact (ha.regs .x23 (by simp [FillCompress.loopRegs])).trans
      (hp.pubs.indices.trans (hb.regs .x23 (by simp [FillCompress.loopRegs])).symm)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.AddressCache.ReadyRelated p pass lane slice old) VG.Impl.Argon2.AArch64.AddressCache.code (fun s t => s.sp = t.sp) :=
  (VG.Proof.Argon2.AArch64.AddressCache.select_public_rel p pass lane slice old).seq VG.Proof.Argon2.AArch64.AddressCache.word_rel

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Source dispatch and cached-word selection use only public addresses and guards. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.RandomSource

structure Related (p : Params) (pass lane slice index old : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old s
  right : VG.Proof.Argon2.AArch64.RandomSource.Ready p pass lane slice index old t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem Related.of_keeps {p : Params} {pass lane slice index old : Nat} {s t a b : State}
    (h : VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old s t)
    (ka : Divide.Keeps ReferenceMap.changed s a) (kb : Divide.Keeps ReferenceMap.changed t b) :
    VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old a b := by
  refine ⟨h.left.of_keeps ka, h.right.of_keeps kb, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.work

theorem test_rel : RelCT isa (fun s t : State => s.sp = t.sp) (.block test)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepare_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old) VG.Impl.Argon2.AArch64.RandomSource.prepare
      (fun s t => VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t) := by
  have trace := AddressMode.code_rel.seq VG.Proof.Argon2.AArch64.RandomSource.test_rel
  have narrowed := trace.mono (P' := VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.AArch64.RandomSource.prepare_ok s p pass lane slice index old h.left,
      VG.Proof.Argon2.AArch64.RandomSource.prepare_ok t p pass lane slice index old h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa.trans fb.symm⟩

theorem Related.cache {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old s t) : AddressCache.ReadyRelated p pass lane slice old s t := by
  refine ⟨h.left.cache.ready, h.right.cache.ready,
    ⟨⟨⟨h.left.cache.layout, h.right.cache.layout, h.bases, h.stacks, h.work⟩,
      h.left.cache.reads, h.right.cache.reads⟩, ?_, ?_, h.left.cache.write, h.right.cache.write⟩⟩
  · exact h.left.filling.position.index.trans h.right.filling.position.index.symm
  · exact h.left.cache.words.counterWord.trans h.right.cache.words.counterWord.symm

theorem code_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old) VG.Impl.Argon2.AArch64.RandomSource.code (fun s t => s.sp = t.sp) := by
  have branches : RelCT isa
      (fun s t => VG.Proof.Argon2.AArch64.RandomSource.Related p pass lane slice index old s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t)
      (.ite (.zero .x .x15) Impl.Argon2.AArch64.DependentWord.code Impl.Argon2.AArch64.AddressCache.code)
      (fun s t => s.sp = t.sp) := by
    apply RelCT.ite (by intro s t h; exact h.2)
    · exact (DependentWord.code_rel p pass lane slice index).mono
        (fun _ _ h => ⟨h.1.1.left.filling, h.1.1.right.filling, h.1.1.bases, h.1.1.stacks, h.1.1.matrices⟩)
        (fun _ _ h => h)
    · exact (AddressCache.code_rel p pass lane slice old).mono
        (fun _ _ h => h.1.1.cache) (fun _ _ h => h)
  exact (VG.Proof.Argon2.AArch64.RandomSource.prepare_rel p pass lane slice index old).seq branches

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillWriteLit`. -/
section
/-! Checked literal of the complete copy/XOR block write. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FillWrite.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.FillWriteCT`. -/
section
/-! Both write paths have a public, fixed sequence of memory accesses. -/
namespace VG.Proof.Argon2.AArch64.FillWrite
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x0, .x1], s.gpr r = t.gpr r) VG.Impl.Argon2.AArch64.FillWrite.code
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x0, .x1])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      exact h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Merged from `Proof.Argon2.AArch64.FillSegmentCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSegmentBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillPointersCT`. -/
section
/-! Pointer setup only branches on the public current column. -/
namespace VG.Proof.Argon2.AArch64.FillPointers
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x24, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    VG.Impl.Argon2.AArch64.FillPointers.code (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x6], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x4, .x24, .x20, .x21, .x22, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [Reg.x6] (by taint_decide)
end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelMappingCT`. -/
section
/-! Reference mapping exposes no more than the permitted reference coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s
  right : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  scratch : work s = work t
  references : Spec.Argon2.reference p pass lane slice index (s.gpr .x0) =
    Spec.Argon2.reference p pass lane slice index (t.gpr .x0)

structure PointerRelated (p : Params) (lane slice index : Nat) (s t : State) : Prop where
  left : Layout p s
  right : Layout p t
  leftPosition : ReferenceMap.Position p lane slice index s
  rightPosition : ReferenceMap.Position p lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  matrices : matrix s = matrix t
  stacks : s.sp = t.sp

theorem lanes_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FillKernel.lanes) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem lanes_ready (s : State) (p : Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.AArch64.FillKernel.Ready p pass lane slice index s) :
    WP isa (.block Impl.Argon2.AArch64.FillKernel.lanes) s fun t =>
      ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps ReferenceMap.changed s t := by
  refine (load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s t := keeps.mono (by decide)
  refine ⟨⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩, k⟩
  · rw [k.rd, k.wr, k.regs .x19 (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using h.layout.frameRead 0 (by simp)
  · rw [k.mem, k.regs .x19 (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord

theorem lanes_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillKernel.Related p pass lane slice index) (.block Impl.Argon2.AArch64.FillKernel.lanes)
      (ReferenceMap.Related p pass lane slice index) := by
  have trace := lanes_rel.mono (P' := VG.Proof.Argon2.AArch64.FillKernel.Related p pass lane slice index)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.AArch64.FillKernel.lanes_ready s p pass lane slice index h.left, VG.Proof.Argon2.AArch64.FillKernel.lanes_ready t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .x19 (by decide)).trans
    (hp.bases.trans (hb.2.regs .x19 (by decide)).symm), eq⟩

theorem mapping_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillKernel.Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.mapping
      (VG.Proof.Argon2.AArch64.FillKernel.PointerRelated p lane slice index) := by
  have trace := (VG.Proof.Argon2.AArch64.FillKernel.lanes_public_rel p pass lane slice index).seq (ReferenceMap.code_rel p pass lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨mapping_ok s p pass lane slice index h.left, mapping_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨hp.left.layout.of_keeps ha.keeps, hp.right.layout.of_keeps hb.keeps,
    hp.left.position.of_keeps ha.keeps, hp.right.position.of_keeps hb.keeps, ?_, ?_, eq⟩
  · exact (ha.keeps.regs .x19 (by decide)).trans (hp.bases.trans (hb.keeps.regs .x19 (by decide)).symm)
  · unfold matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.matrices

theorem matrix_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FillKernel.matrix) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem pointers_trace (p : Params) (lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillKernel.PointerRelated p lane slice index) Impl.Argon2.AArch64.FillKernel.pointers
      (fun s t => s.sp = t.sp) := by
  have trace := matrix_rel.mono (P' := VG.Proof.Argon2.AArch64.FillKernel.PointerRelated p lane slice index)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨load_ok s .x4 232 (by decide) (by decide) (h.left.frameRead 232 (by simp)),
      load_ok t .x4 232 (by decide) (by decide) (h.right.frameRead 232 (by simp))⟩)
  have args : RelCT isa (VG.Proof.Argon2.AArch64.FillKernel.PointerRelated p lane slice index) (.block Impl.Argon2.AArch64.FillKernel.matrix)
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x24, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r) :=
    full.mono (fun _ _ h => h) (by
      intro a b h
      obtain ⟨eq, s, t, hp, ⟨va, ka⟩, ⟨vb, kb⟩⟩ := h
      refine ⟨eq, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact va.trans (hp.matrices.trans vb.symm)
      all_goals rw [ka.regs _ (by decide), kb.regs _ (by decide)]
      · exact hp.leftPosition.current.trans hp.rightPosition.current.symm
      · exact hp.leftPosition.laneLength.trans hp.rightPosition.laneLength.symm
      · exact hp.leftPosition.segmentLength.trans hp.rightPosition.segmentLength.symm
      · exact hp.leftPosition.slice.trans hp.rightPosition.slice.symm
      · exact hp.leftPosition.index.trans hp.rightPosition.index.symm)
  exact (args.seq FillPointers.code_rel).mono (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillCompressOperationCT`. -/
section
/-! Only the compression argument addresses, public frame words and stack
pointer determine the compression-and-write trace. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress

structure Related (s t : State) : Prop where
  left : OperationReady s
  right : OperationReady t
  args : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x19], s.gpr r = t.gpr r
  dest : destination s = destination t
  counter : pass s = pass t
  sp : s.sp = t.sp

structure BeforeWrite (s t : State) : Prop where
  leftRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  rightRead : ∀ d ∈ [0, 16, 248], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8
  bases : s.gpr .x19 = t.gpr .x19
  sp : s.sp = t.sp
  words : ∀ d ∈ [0, 16, 248],
    s.mem.readW (off (s.gpr .x19) d) 64 = t.mem.readW (off (t.gpr .x19) d) 64

theorem called_public {s t a b : State} (hp : VG.Proof.Argon2.AArch64.FillCompress.Related s t)
    (ha : VG.Proof.Argon2.AArch64.FillCompress.Called s a) (hb : VG.Proof.Argon2.AArch64.FillCompress.Called t b) : VG.Proof.Argon2.AArch64.FillCompress.BeforeWrite a b := by
  have abp : a.gpr .x19 = s.gpr .x19 := ha.regs .x19 (by simp [loopRegs])
  have bbp : b.gpr .x19 = t.gpr .x19 := hb.regs .x19 (by simp [loopRegs])
  refine ⟨?_, ?_, abp.trans ((hp.args .x19 (by simp)).trans bbp.symm), ha.sp.trans (hp.sp.trans hb.sp.symm), ?_⟩
  · intro d hd
    rw [ha.rd, ha.wr, abp]; exact hp.left.frameRead d hd
  · intro d hd
    rw [hb.rd, hb.wr, bbp]; exact hp.right.frameRead d hd
  · intro d hd
    rw [abp, bbp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [VG.Proof.Argon2.AArch64.FillCompress.frame_word hp.left ha 0 (by decide), VG.Proof.Argon2.AArch64.FillCompress.frame_word hp.right hb 0 (by decide)]
      exact hp.counter
    · rw [VG.Proof.Argon2.AArch64.FillCompress.frame_word hp.left ha 16 (by decide), VG.Proof.Argon2.AArch64.FillCompress.frame_word hp.right hb 16 (by decide)]
      exact hp.dest
    · rw [VG.Proof.Argon2.AArch64.FillCompress.frame_word hp.left ha 248 (by decide), VG.Proof.Argon2.AArch64.FillCompress.frame_word hp.right hb 248 (by decide),
        hp.left.workWord, hp.right.workWord]
      exact hp.args .x3 (by simp)

theorem call_public_rel : RelCT isa VG.Proof.Argon2.AArch64.FillCompress.Related
    (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.AArch64.compress) VG.Proof.Argon2.AArch64.FillCompress.BeforeWrite := by
  have trace := VG.Proof.Argon2.AArch64.FillCompress.call_rel Spec.Argon2.compressApi.name (P := VG.Proof.Argon2.AArch64.FillCompress.Related) (fun _ _ hp =>
    ⟨hp.left.call, hp.right.call, hp.args .x0 (by simp), hp.args .x1 (by simp),
      hp.args .x2 (by simp), hp.args .x3 (by simp), hp.sp⟩)
  have full := trace.wpDep (fun s t hp =>
    ⟨call_ok _ s hp.left.call, call_ok _ t hp.right.call⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact VG.Proof.Argon2.AArch64.FillCompress.called_public hp ha hb

theorem writeArgs_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block writeArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem writeArgs_public_rel : RelCT isa VG.Proof.Argon2.AArch64.FillCompress.BeforeWrite (.block writeArgs)
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x0, .x1], s.gpr r = t.gpr r) := by
  have trace := writeArgs_rel.mono (P' := VG.Proof.Argon2.AArch64.FillCompress.BeforeWrite) (fun _ _ h => ⟨h.bases, h.sp⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨writeArgs_ok s (hp.leftRead 16 (by simp)) (hp.leftRead 248 (by simp)) (hp.leftRead 0 (by simp)),
      writeArgs_ok t (hp.rightRead 16 (by simp)) (hp.rightRead 248 (by simp)) (hp.rightRead 0 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha.2.2.1.trans ((hp.words 0 (by simp)).trans hb.2.2.1.symm)
  · exact ha.1.trans ((hp.words 16 (by simp)).trans hb.1.symm)
  · exact ha.2.1.trans ((congrArg (· + (4096 : Addr)) (hp.words 248 (by simp))).trans hb.2.1.symm)

theorem operation_rel : RelCT isa VG.Proof.Argon2.AArch64.FillCompress.Related operation (fun s t => s.sp = t.sp) :=
  call_public_rel.seq (writeArgs_public_rel.seq FillWrite.code_rel)

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Merged from `Proof.Argon2.AArch64.FillCompressCT`. -/
section
/-! Compose the setup trace with compression and the full block write. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress

structure CodeRelated (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FillCompress.Ready s
  right : VG.Proof.Argon2.AArch64.FillCompress.Ready t
  args : ∀ r ∈ [Reg.x0, .x1, .x6, .x19], s.gpr r = t.gpr r
  scratch : work s = work t
  counter : pass s = pass t
  sp : s.sp = t.sp

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    VG.Impl.Argon2.AArch64.FillCompress.setup (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepared_public {s t a b : State} (h : VG.Proof.Argon2.AArch64.FillCompress.CodeRelated s t)
    (ha : VG.Proof.Argon2.AArch64.FillCompress.Prepared s a) (hb : VG.Proof.Argon2.AArch64.FillCompress.Prepared t b) : VG.Proof.Argon2.AArch64.FillCompress.Related a b := by
  refine ⟨ha.ready, hb.ready, ?_, ha.dest.trans ((h.args .x6 (by simp)).trans hb.dest.symm),
    ha.counter.trans (h.counter.trans hb.counter.symm), ha.sp.trans (h.sp.trans hb.sp.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((h.args .x0 (by simp)).trans hb.left.symm)
  · exact ha.right.trans ((h.args .x1 (by simp)).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (· + (4096 : Addr)) h.scratch).trans hb.output.symm)
  · exact ha.scratch.trans (h.scratch.trans hb.scratch.symm)
  · exact (ha.regs .x19 (by simp [loopRegs])).trans
      ((h.args .x19 (by simp)).trans (hb.regs .x19 (by simp [loopRegs])).symm)

theorem setup_public_rel : RelCT isa VG.Proof.Argon2.AArch64.FillCompress.CodeRelated VG.Impl.Argon2.AArch64.FillCompress.setup VG.Proof.Argon2.AArch64.FillCompress.Related := by
  have trace := setup_rel.mono (P' := VG.Proof.Argon2.AArch64.FillCompress.CodeRelated)
    (fun _ _ h => ⟨h.args .x19 (by simp), h.sp⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.FillCompress.setup_ok s h.left, VG.Proof.Argon2.AArch64.FillCompress.setup_ok t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact VG.Proof.Argon2.AArch64.FillCompress.prepared_public hp ha hb

theorem code_rel : RelCT isa VG.Proof.Argon2.AArch64.FillCompress.CodeRelated VG.Impl.Argon2.AArch64.FillCompress.code (fun s t => s.sp = t.sp) :=
  setup_public_rel.seq VG.Proof.Argon2.AArch64.FillCompress.operation_rel

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Equal permitted references give equal compression and block-update traces. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem prepared_public {p : Params} {pass lane slice index : Nat} {s t a b : State}
    (h : VG.Proof.Argon2.AArch64.FillKernel.Related p pass lane slice index s t)
    (ha : VG.Proof.Argon2.AArch64.FillKernel.Prepared s a p pass lane slice index) (hb : VG.Proof.Argon2.AArch64.FillKernel.Prepared t b p pass lane slice index) :
    FillCompress.CodeRelated a b := by
  have currentEq : current s p lane slice index = current t p lane slice index := by
    unfold current; rw [h.matrices]
  have previousEq : previous s p lane slice index = previous t p lane slice index := by
    unfold previous; rw [h.matrices]
  have referenceEq : referenced s p pass lane slice index = referenced t p pass lane slice index := by
    unfold referenced; rw [h.references, h.matrices]
  have workA : FillCompress.work a = work s := by
    unfold FillCompress.work work; rw [ha.keeps.regs .x19 (by decide), ha.keeps.mem]
  have workB : FillCompress.work b = work t := by
    unfold FillCompress.work work; rw [hb.keeps.regs .x19 (by decide), hb.keeps.mem]
  have passA : FillCompress.pass a = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [ha.keeps.regs .x19 (by decide), ha.keeps.mem]
    exact h.left.passWord
  have passB : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [hb.keeps.regs .x19 (by decide), hb.keeps.mem]
    exact h.right.passWord
  refine ⟨ha.ready, hb.ready, ?_, workA.trans (h.scratch.trans workB.symm), passA.trans passB.symm, ha.keeps.sp.trans (h.stacks.trans hb.keeps.sp.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha.previousPtr.trans (previousEq.trans hb.previousPtr.symm)
  · exact ha.referencePtr.trans (referenceEq.trans hb.referencePtr.symm)
  · exact ha.currentPtr.trans (currentEq.trans hb.currentPtr.symm)
  · exact (ha.keeps.regs .x19 (by decide)).trans (h.bases.trans (hb.keeps.regs .x19 (by decide)).symm)

theorem prepare_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillKernel.Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.prepare
      FillCompress.CodeRelated := by
  have trace := (VG.Proof.Argon2.AArch64.FillKernel.mapping_public_rel p pass lane slice index).seq (VG.Proof.Argon2.AArch64.FillKernel.pointers_trace p lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.AArch64.FillKernel.prepare_ok s p pass lane slice index h.left, VG.Proof.Argon2.AArch64.FillKernel.prepare_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact VG.Proof.Argon2.AArch64.FillKernel.prepared_public hp ha hb

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillKernel.Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.code
      (fun s t => s.sp = t.sp) := (VG.Proof.Argon2.AArch64.FillKernel.prepare_public_rel p pass lane slice index).seq FillCompress.code_rel

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Merged from `Proof.Argon2.AArch64.FillBlockCounter`. -/
section
/-! Compression preserves the public cache counter selected by the random source. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

theorem counter_run {s t : State} {trace : List Leak} {p : Params} {pass lane slice index old : Nat}
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (run : Exec isa Impl.Argon2.AArch64.FillBlock.code s trace t) :
    t.mem.readW (off (t.gpr .x19) 8) 64 = RandomSource.counterValue p pass slice index old := by
  cases run with
  | seq sourceRun kernelRun =>
    obtain ⟨_, a', runA, source⟩ := RandomSource.code_ok s p pass lane slice index old h state represented
    obtain ⟨_, rfl⟩ := Exec.det sourceRun runA
    obtain ⟨_, a', counterRun, counter⟩ := RandomSource.counter_ok s p pass lane slice index old h
    obtain ⟨_, rfl⟩ := Exec.det sourceRun counterRun
    obtain ⟨_, ready⟩ := source.ready
    obtain ⟨_, t', runT, done⟩ := FillKernel.code_ok _ p pass lane slice index ready.filling
    obtain ⟨_, rfl⟩ := Exec.det kernelRun runT
    exact (done.frame_word ready.filling 8 (by decide) (by decide)).trans counter

end VG.Proof.Argon2.AArch64.FillBlock
end

/-! Merged from `Proof.Argon2.AArch64.FillBlockCT`. -/
section
/-! An active filling cell leaks only its specified data-dependent reference. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  references : independent p pass slice = false →
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory)

theorem Related.of_indices {p : Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (source : RandomSource.Related p pass lane slice index old s t)
    (leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory)
    (rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory)
    (indices : (fillBlock p pass slice lane index leftState).indices =
      (fillBlock p pass slice lane index rightState).indices) :
    VG.Proof.Argon2.AArch64.FillBlock.Related p pass lane slice index old leftState rightState s t := by
  refine ⟨source, leftMatrix, rightMatrix, ?_⟩
  intro mode
  rw [Proof.Argon2.FillStep.indices p pass lane slice index leftState source.left.filling.bounds.active,
    Proof.Argon2.FillStep.indices p pass lane slice index rightState source.right.filling.bounds.active] at indices
  simp only [mode, Bool.false_eq_true, ite_false] at indices
  exact (List.cons.inj indices).1

theorem Related.reference_eq {p : Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (h : VG.Proof.Argon2.AArch64.FillBlock.Related p pass lane slice index old leftState rightState s t) :
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory) := by
  cases mode : independent p pass slice
  · exact h.references mode
  · simp only [Proof.Argon2.FillStep.random, mode, ite_true]

theorem source_public_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillBlock.Related p pass lane slice index old leftState rightState)
      Impl.Argon2.AArch64.RandomSource.code (FillKernel.Related p pass lane slice index) := by
  intro s t ta tb a b hp ea eb
  obtain ⟨traces, _⟩ := RandomSource.code_rel p pass lane slice index old _ _ _ _ _ _ hp.source ea eb
  obtain ⟨_, a', runA, ha⟩ := RandomSource.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
  obtain ⟨_, b', runB, hb⟩ := RandomSource.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
  obtain ⟨_, sameA⟩ := Exec.det ea runA
  obtain ⟨_, sameB⟩ := Exec.det eb runB
  subst a'; subst b'
  refine ⟨traces, ?_⟩
  obtain ⟨_, readyA⟩ := ha.ready
  obtain ⟨_, readyB⟩ := hb.ready
  refine ⟨readyA.filling, readyB.filling, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.source.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm)
  · exact ha.sp.trans
      (hp.source.stacks.trans hb.sp.symm)
  · exact (ha.frame_word hp.source.left 232 (by decide) (by decide)).trans
      (hp.source.matrices.trans (hb.frame_word hp.source.right 232 (by decide) (by decide)).symm)
  · exact (ha.frame_word hp.source.left 248 (by decide) (by decide)).trans
      (hp.source.work.trans (hb.frame_word hp.source.right 248 (by decide) (by decide)).symm)
  · rw [ha.random, hb.random]; exact hp.reference_eq

theorem code_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillBlock.Related p pass lane slice index old leftState rightState)
      Impl.Argon2.AArch64.FillBlock.code (fun s t => s.sp = t.sp) :=
  (VG.Proof.Argon2.AArch64.FillBlock.source_public_rel p pass lane slice index old leftState rightState).seq
    (FillKernel.code_rel p pass lane slice index)

end VG.Proof.Argon2.AArch64.FillBlock
end

/-! Public counters and coordinates remain related across a segment iteration. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSegment

theorem advance_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x21, .x23], s.gpr r = t.gpr r)
    (.block VG.Impl.Argon2.AArch64.FillSegment.advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x21, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass lane slice index : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : ∃ old, RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (FillBlock.Related p pass lane slice index old leftState rightState) VG.Impl.Argon2.AArch64.FillSegment.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (index + 1 < p.segmentLen →
        VG.Proof.Argon2.AArch64.FillSegment.NextRelated p pass lane slice (index + 1)
          (fillBlock p pass slice lane index leftState) (fillBlock p pass slice lane index rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA advanceA =>
    cases eb with
    | seq fillB advanceB =>
      obtain ⟨filledTrace, filledSp⟩ := FillBlock.code_rel p pass lane slice index old leftState rightState
        _ _ _ _ _ _ hp fillA fillB
      obtain ⟨_, sa, runA, filledA⟩ := FillBlock.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillBlock.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain ⟨counterA, readyA⟩ := filledA.ready
      obtain ⟨counterB, readyB⟩ := filledB.ready
      obtain ⟨advancedTrace, _⟩ := VG.Proof.Argon2.AArch64.FillSegment.advance_rel _ _ _ _ _ _ (by
        refine ⟨filledSp, ?_⟩
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact readyA.filling.position.segmentLength.trans readyB.filling.position.segmentLength.symm
        · exact readyA.filling.position.index.trans readyB.filling.position.index.symm) advanceA advanceB
      obtain ⟨_, a', advanceRunA, valueA, flagA, keptA⟩ := VG.Proof.Argon2.AArch64.FillSegment.advance_nat_ok _ p pass lane slice index readyA.filling
      obtain ⟨_, b', advanceRunB, valueB, flagB, keptB⟩ := VG.Proof.Argon2.AArch64.FillSegment.advance_nat_ok _ p pass lane slice index readyB.filling
      obtain ⟨_, rfl⟩ := Exec.det advanceA advanceRunA
      obtain ⟨_, rfl⟩ := Exec.det advanceB advanceRunB
      refine ⟨by rw [filledTrace, advancedTrace], flagA.trans flagB.symm, ?_⟩
      intro active
      have nextA := VG.Proof.Argon2.AArch64.FillSegment.next_ready readyA keptA valueA active
      have nextB := VG.Proof.Argon2.AArch64.FillSegment.next_ready readyB keptB valueB active
      have counterWordA := FillBlock.counter_run hp.source.left leftState hp.leftMatrix fillA
      have counterWordB := FillBlock.counter_run hp.source.right rightState hp.rightMatrix fillB
      have wordEq : BitVec.ofNat 64 counterA = BitVec.ofNat 64 counterB :=
        readyA.cache.words.counterWord.symm.trans
          (counterWordA.trans (counterWordB.symm.trans readyB.cache.words.counterWord))
      have counters := (ReferenceMap.word_eq counterA counterB readyA.cache.bound readyB.cache.bound).mp wordEq
      subst counterB
      refine ⟨⟨counterA, nextA, nextB, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [keptA.regs .x19 (by decide), keptB.regs .x19 (by decide),
          filledA.regs .x19 (by simp [FillCompress.loopRegs]), filledB.regs .x19 (by simp [FillCompress.loopRegs])]
        exact hp.source.bases
      · rw [keptA.sp, keptB.sp, filledA.sp, filledB.sp]
        exact hp.source.stacks
      · unfold FillKernel.matrix
        rw [keptA.mem, keptB.mem, keptA.regs .x19 (by decide), keptB.regs .x19 (by decide)]
        exact filledA.matrix.trans (hp.source.matrices.trans filledB.matrix.symm)
      · unfold AddressCalls.work
        rw [keptA.mem, keptB.mem, keptA.regs .x19 (by decide), keptB.regs .x19 (by decide)]
        exact filledA.work.trans (hp.source.work.trans filledB.work.symm)
      · unfold FillKernel.matrix
        rw [keptA.mem, keptA.regs .x19 (by decide)]
        exact filledA.represented
      · unfold FillKernel.matrix
        rw [keptB.mem, keptB.regs .x19 (by decide)]
        exact filledB.represented

end VG.Proof.Argon2.AArch64.FillSegment
end

/-! The segment loop exposes only the reviewed segment reference log. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice index count leftState).indices =
    (Proof.Argon2.segment p pass lane slice index count rightState).indices

theorem loop_rel (p : Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillSegment.Related p pass lane slice index count old leftState rightState)
      Impl.Argon2.AArch64.FillSegment.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (index old : Nat) (leftState rightState : FillState),
    index + n = p.segmentLen ∧ 0 < n ∧ VG.Proof.Argon2.AArch64.FillSegment.Related p pass lane slice index n old leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillSegment.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, counter, ls, rs, endIndex, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have blockRelated : FillBlock.Related p pass lane slice j counter ls rs s t :=
        ⟨hp.source, hp.leftMatrix, hp.rightMatrix,
          Proof.Argon2.segment_first_reference p pass lane slice j n ls rs
            hp.source.left.filling.bounds.active hp.indices⟩
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.AArch64.FillSegment.body_rel p pass lane slice j counter ls rs _ _ _ _ _ _ blockRelated ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.AArch64.FillSegment.body_ok s p pass lane slice j counter hp.source.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.segmentLen := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨⟨nextCounter, ready⟩, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at indices
        exact ⟨n, by omega, j + 1, nextCounter, fillBlock p pass slice lane j ls,
          fillBlock p pass slice lane j rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨index, old, leftState, rightState, endIndex, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillSegment
end

/-! Complete segment setup and filling expose only the specified reference log. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Related (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : VG.Proof.Argon2.AArch64.SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState).indices =
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState).indices

structure PreparedRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  left : FillContext.Ready p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0 s
  right : FillContext.Ready p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0 t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) leftState).indices =
    (Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) rightState).indices

theorem prepare_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.Related p pass lane slice leftState rightState) VG.Impl.Argon2.AArch64.SegmentSetup.prepare
      (VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState) := by
  have trace := (VG.Proof.Argon2.AArch64.SegmentSetup.prepare_trace p pass lane slice).mono
    (P' := VG.Proof.Argon2.AArch64.SegmentSetup.Related p pass lane slice leftState rightState) (fun _ _ h => h.ready) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.SegmentSetup.prepare_ok s p pass lane slice h.ready.left, VG.Proof.Argon2.AArch64.SegmentSetup.prepare_ok t p pass lane slice h.ready.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.context, hb.context, ?_, ?_, ha.matrix.trans (hp.ready.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.ready.work.trans hb.work.symm), ha.represents hp.ready.left leftState.memory hp.leftMatrix,
    hb.represents hp.ready.right rightState.memory hp.rightMatrix, ?_⟩
  · rw [ha.regs .x19 (by simp [FillCompress.loopRegs]) (by decide), hb.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
    exact hp.ready.bases
  · rw [ha.sp, hb.sp]
    exact hp.ready.stacks
  · have indices := hp.indices
    rw [Proof.Argon2.segment_start p pass lane slice leftState hp.ready.left.parameters.segment_bound.1,
      Proof.Argon2.segment_start p pass lane slice rightState hp.ready.right.parameters.segment_bound.1] at indices
    exact indices

theorem PreparedRelated.of_keeps {p : Params} {pass lane slice : Nat} {leftState rightState : FillState}
    {s t a b : State} (h : VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState s t)
    (ka : Divide.Keeps [.x14, .x15] s a) (kb : Divide.Keeps [.x14, .x15] t b) :
    VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState a b := by
  refine ⟨h.left.of_keeps (ka.mono (by decide)), h.right.of_keeps (kb.mono (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, h.indices⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.work
  · unfold FillKernel.matrix; rw [ka.mem, ka.regs .x19 (by decide)]; exact h.leftMatrix
  · unfold FillKernel.matrix; rw [kb.mem, kb.regs .x19 (by decide)]; exact h.rightMatrix

theorem check_context_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : FillContext.Ready p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0 s) : WP isa (.block check) s fun t =>
      eval (.nonzero .x .x14) t = some (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen)) ∧ Divide.Keeps [.x14, .x15] s t := by
  have minimum := h.parameters.segment_bound
  have segmentBound : p.segmentLen < 2 ^ 63 := by
    have laneLe : p.laneLen ≤ p.blocks := by
      rw [Proof.Argon2.blocks_lanes p h.parameters.lanesPositive]
      exact Nat.le_mul_of_pos_left _ h.parameters.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.parameters.lanesPositive
    have blocks := Proof.Argon2.blocks_le_memory p
    have memoryBound := h.parameters.memoryBound
    omega
  have startBound := Nat.lt_of_le_of_lt (VG.Proof.Argon2.AArch64.SegmentSetup.start_le pass slice p.segmentLen minimum.1) segmentBound
  have left : (s.gpr .x23).toNat < 2 ^ 63 := by
    rw [h.position.index, ReferenceMap.word_nat _ (Nat.lt_trans startBound (by decide))]; exact startBound
  have right : (s.gpr .x21).toNat < 2 ^ 63 := by
    rw [h.position.segmentLength, ReferenceMap.word_nat _ minimum.2]; exact segmentBound
  refine (VG.Proof.Argon2.AArch64.SegmentSetup.check_ok s left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, h.position.index, h.position.segmentLength,
    ReferenceMap.word_nat (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) (Nat.lt_of_le_of_lt (VG.Proof.Argon2.AArch64.SegmentSetup.start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem check_trace : RelCT isa (fun s t : State => s.sp = t.sp)
    (.block check) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem check_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState) (.block check)
      (fun s t => VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState s t ∧
        eval (.nonzero .x .x14) s = some (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen)) ∧ eval (.nonzero .x .x14) t = some (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen))) := by
  have trace := check_trace.mono (P' := VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.SegmentSetup.check_context_ok s p pass lane slice h.left, VG.Proof.Argon2.AArch64.SegmentSetup.check_context_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa, fb⟩

theorem code_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.SegmentSetup.Related p pass lane slice leftState rightState) VG.Impl.Argon2.AArch64.SegmentSetup.code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => VG.Proof.Argon2.AArch64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState s t ∧
        eval (.nonzero .x .x14) s = some (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen)) ∧ eval (.nonzero .x .x14) t = some (decide (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen)))
      (.ite (.nonzero .x .x14) Impl.Argon2.AArch64.FillSegment.loop (.block [])) (fun _ _ => True) := by
    refine RelCT.ite (by intro s t h; simp only [h.2.1, h.2.2]) ?_ ?_
    · intro s t ts tt a b hp ea eb
      have active : VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice < p.segmentLen := by
        have taken := hp.2
        simp only [hp.1.2.1, Option.some.injEq, decide_eq_true_eq] at taken
        exact taken
      have left := hp.1.1.left.activate active (VG.Proof.Argon2.AArch64.SegmentSetup.start_active pass slice)
      have right := hp.1.1.right.activate active (VG.Proof.Argon2.AArch64.SegmentSetup.start_active pass slice)
      have related : FillSegment.Related p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice)
          (p.segmentLen - VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0 leftState rightState s t :=
        ⟨⟨left, right, hp.1.1.bases, hp.1.1.stacks, hp.1.1.matrices, hp.1.1.work⟩,
          hp.1.1.leftMatrix, hp.1.1.rightMatrix, hp.1.1.indices⟩
      exact FillSegment.loop_rel p pass lane slice (VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.AArch64.SegmentSetup.start pass slice) 0
        leftState rightState (by omega) (by omega) _ _ _ _ _ _ related ea eb
    · intro s t ts tt a b hp ea eb
      cases ea with
      | block runA =>
        cases eb with
        | block runB =>
          obtain ⟨rfl, rfl⟩ := runA
          obtain ⟨rfl, rfl⟩ := runB
          exact ⟨rfl, trivial⟩
  exact (VG.Proof.Argon2.AArch64.SegmentSetup.prepare_public_rel p pass lane slice leftState rightState).seq
    ((VG.Proof.Argon2.AArch64.SegmentSetup.check_public_rel p pass lane slice leftState rightState).seq branches)

end VG.Proof.Argon2.AArch64.SegmentSetup

end
