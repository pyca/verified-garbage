module

public import VerifiedGarbage.Impl.Argon2.AArch64.FillFinish
public import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
public import VerifiedGarbage.Impl.Argon2.AArch64.FillIteration
public import VerifiedGarbage.Impl.Argon2.AArch64.FillSlices
public import VerifiedGarbage.Impl.Argon2.AArch64.FillSlice
public import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes
public import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.FillLaneAdvance
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup
public import VerifiedGarbage.Proof.Argon2.Lanes
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Iterations
public import VerifiedGarbage.Proof.Argon2.AArch64.FinishReady
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.AArch64.ReductionLoopState
public import VerifiedGarbage.Proof.Argon2.Contract

/-! ### `Argon2.AArch64.FillIterations`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillIterationsBody`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillIteration`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSlices`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSlicesBody`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillSlice`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillLanes`, which only this module used -/

section

/-! ### `Argon2.AArch64.FillLanesBody`, which only this module used -/

section

/-! One lane iteration fills its segment and advances the public lane. -/

@[expose] public section

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
    WP isa Impl.Argon2.AArch64.FillLanes.body s (Done s · p pass lane slice state) := by
  unfold Impl.Argon2.AArch64.FillLanes.body
  refine WP.seq ((SegmentSetup.code_ok s p pass lane slice h state represented).mono ?_)
  intro a filled
  have ready := finished_ready h.parameters filled
  obtain ⟨old, words⟩ := ready.words
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [words.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.parameters.laneBound
  have lanesBound32 := h.parameters.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega_using [laneBound, lanesBound32])]; omega_using [laneBound, lanesBound32]
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [ready.lanesWord, ReferenceMap.word_nat p.lanes (by omega_using [lanesBound32])]; omega_using [lanesBound32]
  refine (advance_ok a (ready.layout.frameRead 184 (by simp)) left right).mono ?_
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
  · rw [flag, added, ready.lanesWord, ReferenceMap.word_nat (lane + 1) (by omega_using [laneBound, lanesBound32]),
      ReferenceMap.word_nat p.lanes lanesBound]
  · intro active; exact change_lane_ready ready keeps nextWord active

end VG.Proof.Argon2.AArch64.FillLanes

end

end


/-! Termination and correctness of all remaining lanes in one slice. -/

@[expose] public section

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
    (h : Done s t p pass lane slice state) (last : lane + 1 = p.lanes) :
    Finished s t p pass slice (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) := by
  obtain ⟨a, ready, keeps⟩ := h.header
  exact ⟨h.represented, h.matrix, h.work, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.sp,
    h.regs, lane, a, last, ready, keeps⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice : Nat} {state finalState : FillState}
    (first : Done s a p pass lane slice state) (rest : Finished a t p pass slice finalState) :
    Finished s t p pass slice finalState := by
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
      (Finished s · p pass slice (Proof.Argon2.lanes p pass slice lane count state)) := by
  induction count generalizing s lane state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass lane slice h state represented
    rw [Proof.Argon2.lanes_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega_using [endLane]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) done.represented (by omega_using []) (by omega_using [endLane])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.FillLanes

end

end


/-! Merged from `Proof.Argon2.AArch64.FillSlicePrepare`. -/

@[expose] public section

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
    (h : SegmentSetup.Ready p pass lane slice s) : Ready p pass lane slice s :=
  ⟨h.layout, h.addressLayout, h.reads, h.write, h.words, h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.segment {p : Params} {pass lane slice : Nat} {s : State}
    (h : Ready p pass lane slice s) (parameters : FillContext.Parameters p pass lane slice) :
    SegmentSetup.Ready p pass lane slice s :=
  ⟨parameters, h.layout, h.addressLayout, h.reads, h.write, h.words,
    h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.of_state {p : Params} {pass lane slice newLane newSlice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x20, .x21], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (laneWord : t.gpr .x24 = BitVec.ofNat 64 newLane) (sliceWord : t.gpr .x22 = BitVec.ofNat 64 newSlice) :
    Ready p pass newLane newSlice t := by
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
    (h : FillLanes.Finished s t p pass slice state) : Ready p pass p.lanes slice t := by
  obtain ⟨lane, a, _, ready, keeps⟩ := h.header
  obtain ⟨old, words⟩ := ready.words
  apply (of_segment_ready ready).of_state _ keeps.sp keeps.mem keeps.rd keeps.wr h.laneWord
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

theorem setup_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) :
    WP isa (.block Impl.Argon2.AArch64.FillSlice.setup) s (Prepared s · p pass slice) := by
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

theorem code_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlice.code s
      (FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice 0 p.lanes state)) := by
  unfold Impl.Argon2.AArch64.FillSlice.code
  refine WP.seq ((setup_ok s p pass slice h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillLanes.loop_ok p.lanes a p pass 0 slice prepared.ready state representedA
    h.parameters.lanesPositive (by omega_using [])).mono ?_
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

end


/-! Merged from `Proof.Argon2.AArch64.FillSliceAdvance`. -/

@[expose] public section

section
/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_ok (s : State) (ha : (s.gpr .x22 + 1).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t => t.gpr .x22 = s.gpr .x22 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x22 + 1).toNat < 4)) ∧
      Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil,
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
    WP isa Impl.Argon2.AArch64.FillSlices.body s (Done s · p pass slice state) := by
  unfold Impl.Argon2.AArch64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  have sliceBound := h.parameters.sliceBound
  have added : a.gpr .x22 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have inputBound : (a.gpr .x22 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (slice + 1) (by omega_using [sliceBound])]; omega_using [sliceBound]
  refine (advance_ok a inputBound).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have nextWord := value.trans added
  have nextHeader := advanced_header header keeps nextWord
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
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega_using [sliceBound])]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.AArch64.FillSlices

end

end


/-! Termination and correctness of the four-slice filling pass. -/

@[expose] public section

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
    (h : Done s t p pass slice state) (last : slice + 1 = 4) :
    Finished s t p pass (Proof.Argon2.lanes p pass slice 0 p.lanes state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass slice : Nat} {state finalState : FillState}
    (first : Done s a p pass slice state) (rest : Finished a t p pass finalState) : Finished s t p pass finalState := by
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
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (Finished s · p pass (Proof.Argon2.slices p pass slice count state)) := by
  induction count generalizing s slice state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass slice h state represented
    rw [Proof.Argon2.slices_succ]
    cases n with
    | zero =>
      have last : slice + 1 = 4 := endSlice
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : slice + 1 < 4 := by omega_using [endSlice]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (slice + 1) (done.next active)
        (Proof.Argon2.lanes p pass slice 0 p.lanes state) done.represented (by omega_using []) (by omega_using [endSlice])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem pass_ok (s : State) (p : Params) (pass : Nat) (h : FillSlice.Ready p pass 0 s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (Finished s · p pass (fillPass p state pass)) := by
  rw [← Proof.Argon2.slices_pass p pass state]
  exact loop_ok 4 s p pass 0 h state represented (by decide) (by decide)

end VG.Proof.Argon2.AArch64.FillSlices

end

end


/-! Merged from `Proof.Argon2.AArch64.FillIterationPrepare`. -/

@[expose] public section

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

theorem setup_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) :
    WP isa (.block Impl.Argon2.AArch64.FillIteration.setup) s (Prepared s · p pass) := by
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

theorem code_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.AArch64.FillIteration.code
  refine WP.seq ((setup_ok s p pass h).mono ?_)
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

end


/-! Merged from `Proof.Argon2.AArch64.FillPassSave`. -/

@[expose] public section

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
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) : WP isa advance s (Saved s) := by
  unfold advance
  refine WP.seq ((increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have readA : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (off (a.gpr .x19) 0) 8 := by rw [keeps.wr, bp]; exact write
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (saveCheck_ok a writeA readA left right).mono ?_
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

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega_using [separate]) (by omega_using [bound]) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
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
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
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
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x19, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : Params} (h : Saved s t) : Frame (writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .x19, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.represents {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) (blocks : Array Block)
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
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (pass + 1 < p.passes))
  next : pass + 1 < p.passes → Ready p (pass + 1) t

theorem body_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIterations.body s (Done s · p pass state) := by
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
    rw [words.passWord, added, ReferenceMap.word_nat (pass + 1) (by omega_using [passBound])]; omega_using [passBound]
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [words.passesWord, ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
    exact Nat.lt_trans h.passesBound (by decide)
  refine (advance_ok a (filled.header.reads 0 (by simp)) write
    (filled.header.reads 72 (by simp)) left right).mono ?_
  intro t saved
  have header := saved.header filled.header
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.sp.trans filled.sp, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [writes, filled.matrix, filled.work,
      filled.sp,
      filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at lastFrame
    exact (filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x8, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega_using [passBound]),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .x19 (by decide)]; exact write

end VG.Proof.Argon2.AArch64.FillIterations

end

end


/-! Termination and correctness of every requested filling pass. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p p.passes p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (h : Done s t p pass state) (last : pass + 1 = p.passes) : Finished s t p (fillPass p state pass) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass : Nat} {state finalState : FillState}
    (first : Done s a p pass state) (rest : Finished a t p finalState) : Finished s t p finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    WP isa Impl.Argon2.AArch64.FillIterations.loop s (Finished s · p (Proof.Argon2.iterations p pass count state)) := by
  induction count generalizing s pass state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass h state represented
    rw [Proof.Argon2.iterations_succ]
    cases n with
    | zero =>
      have last : pass + 1 = p.passes := endPass
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : pass + 1 < p.passes := by omega_using [endPass]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (pass + 1) (done.next active)
        (fillPass p state pass) done.represented (by omega_using []) (by omega_using [endPass])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem Finished.frame_word {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (ready : Ready p pass s) (done : Finished s t p state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : 24 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
  obtain ⟨lane, slice, header⟩ := ready.filling.header
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact header.layout.matrixFrame.symm.sub_left sub
    · exact header.addressLayout.frameWork.sub_left sub
    · exact header.addressLayout.frameStack.sub_left sub
    · simpa only [off, BitVec.add_zero] using Offset.disjoint (d := d) (n := 8) (e := 0) (k := 24) (s.gpr .x19) (Or.inr (by omega_using [separate])) (by omega_using [bound]) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.FillIterations

end

end


/-! Merged from `Proof.Argon2.AArch64.FinishStage`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.FinalOutput`. -/
section
/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (output s) p.tagLen = finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨output s, p.tagLen⟩, ⟨work s, 16384⟩, below s.sp 16] s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.AArch64.FinalOutput.code name v.hash) s (Done s · p memory) := by
  unfold Impl.Argon2.AArch64.FinalOutput.code
  refine WP.seq ((args_ok s h.reads).mono ?_)
  intro a args
  have length := args.outputLength.trans h.tagWord
  refine (FinalCall.hPrime_call_ok v name p.tagLen a (args.ready h) args.inputLength length).mono ?_
  intro t called
  refine ⟨?_, fun r hr => (called.regs r hr).trans (args.regs r hr), called.sp.trans args.keeps.sp, called.rd.trans args.keeps.rd,
    called.wr.trans args.keeps.wr, ?_⟩
  · have input : bytesAt a.mem (a.gpr .x0) 1024 =
        serialize (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) := by
      rw [args.keeps.mem, args.input, ← Proof.Argon2.serialize_blockAt, block]
    rw [Proof.Argon2.finish_reduction]
    have digest := called.digest
    rw [args.output, input] at digest
    exact digest
  · have frame := called.frame
    rw [args.output, args.work, args.keeps.sp, args.keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! The complete reviewed finish computation, with its enclosing frame and ABI obligations. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

def writes (s : State) (p : Params) : List Region :=
  [⟨matrix s, 1024⟩, ⟨FinalOutput.output s, p.tagLen⟩,
    ⟨FinalOutput.work s, 16384⟩, below s.sp 16]

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = Spec.Argon2.finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa (Impl.Argon2.AArch64.Finish.code name v.hash) s (Done s · p memory) := by
  unfold Impl.Argon2.AArch64.Finish.code
  refine WP.seq ((FinalReduction.code_ok s p h.reduction memory represented).mono ?_)
  intro a reduced
  refine (FinalOutput.code_ok v name a p (output_ready h reduced) memory reduced.represented.accumulator).mono ?_
  intro t written
  have output : FinalOutput.output a = FinalOutput.output s := frame_word h.reduction reduced 256 (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := frame_word h.reduction reduced 248 (by decide)
  refine ⟨?_, fun r hr bx => (written.regs r hr).trans (reduced.regs r hr bx),
    written.sp.trans reduced.sp, written.rd.trans reduced.rd, written.wr.trans reduced.wr, ?_⟩
  · have digest := written.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := reduced.frame.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, by simp [writes], fun _ h => h⟩)
    have lastFrame := written.frame
    rw [output, work, reduced.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.Finish
end

/-! Merged from `Proof.Argon2.AArch64.FillFinishReady`. -/
section
/-! The complete filling loop retains the original final-call allocations and public metadata. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

theorem finish_ready {s t : State} {p : Params} {state : FillState}
    (filling : FillIterations.Ready p 0 s) (ready : Finish.Ready p s)
    (done : FillIterations.Finished s t p state) : Finish.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)
  have sp := done.sp
  have base : matrix t = matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word filling 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word filling 248 (by decide) (by decide)
  constructor
  · have a := ready.reduction.allocation
    refine ⟨⟨a.positive, a.minimum, a.bound, ?_, ?_, ?_, ?_⟩, ready.reduction.lanesBound, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact a.read
    · rw [base, done.wr]; exact a.write
    · rw [base, bp]; exact a.frame
    · exact (done.regs .x20 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans a.length
    · rw [done.rd, done.wr, bp]; exact ready.reduction.lanesRead
    · exact (done.frame_word filling 184 (by decide) (by decide)).trans ready.reduction.lanesWord
  · refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
      (done.frame_word filling 264 (by decide) (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sp]; exact ready.output.stackMinimum
    · rw [done.rd, done.wr, bp]; exact ready.output.reads
    · rw [base, done.rd, done.wr]; exact ready.output.input
    · rw [output, done.wr]; exact ready.output.outputWrite
    · rw [work, done.wr]; exact ready.output.workWrite
    · rw [base, work]; exact ready.output.inputWork
    · rw [output, work]; exact ready.output.outputWork
    · rw [sp, base]; exact ready.output.stackInput
    · rw [sp, output]; exact ready.output.stackOutput
    · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.FillFinish
end

/-! The complete filling and finalization stages produce the reviewed final tag. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  filling : FillIterations.Ready p 0 s
  finish : Finish.Ready p s
  positive : 0 < p.passes

def writes (s : State) (p : Params) : List Region := FillIterations.writes s p ++ Finish.writes s p

structure Done (s t : State) (p : Params) (state : FillState) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen =
    Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes state).memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.AArch64.FillFinish.code name v.hash) s (Done s · p state) := by
  unfold Impl.Argon2.AArch64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : matrix a = matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.sp.trans filled.sp, finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := filled.frame.sub (by
      intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    have lastFrame := finished.frame
    rw [Finish.writes, base, output, work,
      filled.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

end VG.Proof.Argon2.AArch64.FillFinish
