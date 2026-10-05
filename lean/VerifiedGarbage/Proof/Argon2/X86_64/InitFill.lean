import VerifiedGarbage.Impl.Argon2.X86_64.FillFinish
import VerifiedGarbage.Impl.Argon2.X86_64.FillIterations
import VerifiedGarbage.Impl.Argon2.X86_64.FillIteration
import VerifiedGarbage.Impl.Argon2.X86_64.FillSlices
import VerifiedGarbage.Impl.Argon2.X86_64.FillSlice
import VerifiedGarbage.Impl.Argon2.X86_64.FillLanes
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Impl.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillSegment
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput
import VerifiedGarbage.Impl.Argon2.X86_64.FinalReduction
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Impl.Argon2.X86_64.ReductionInit
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Impl.Argon2.X86_64.ReduceLanes
import VerifiedGarbage.Impl.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Impl.Argon2.X86_64.InitFill
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Argon2.X86_64.FillSetup
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite
import VerifiedGarbage.Impl.Argon2.X86_64.AddressMode
import VerifiedGarbage.Impl.Argon2.X86_64.DependentWord
import VerifiedGarbage.Impl.Argon2.X86_64.FirstLane
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceStart

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupPrepare`. -/
section

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupSteps`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillContext`. -/
section
/-! A segment context allows its starting and final indices, including an empty suffix. -/

namespace VG.Proof.Argon2.X86_64.FillContext

open VG VG.X86_64 VG.Spec.Argon2

structure Parameters (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4

structure Ready (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) (s : State) : Prop where
  parameters : VG.Proof.Argon2.X86_64.FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  position : ReferenceMap.Position p lane slice index s
  lanesWord : s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.activate {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s : State}
    (h : VG.Proof.Argon2.X86_64.FillContext.Ready p pass lane slice index old s) (bound : index < p.segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) : RandomSource.Ready p pass lane slice index old s :=
  ⟨⟨h.layout, ⟨h.parameters.lanesPositive, h.parameters.lanesBound, h.parameters.memoryMinimum,
    h.parameters.memoryBound, h.parameters.passBound, h.parameters.laneBound, h.parameters.sliceBound,
    bound, active⟩, h.position, h.cache.words.passWord, h.lanesWord⟩, h.cache, h.matrixWork⟩

theorem Parameters.segment_bound {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} (h : VG.Proof.Argon2.X86_64.FillContext.Parameters p pass lane slice) :
    2 ≤ p.segmentLen ∧ p.segmentLen < 2 ^ 64 := by
  have minimum := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have le : p.segmentLen ≤ p.blocks := by
    have blocks := Proof.Argon2.blocks_lanes p h.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
    have laneLe : p.laneLen ≤ p.blocks := by rw [blocks]; exact Nat.le_mul_of_pos_left _ h.lanesPositive
    omega
  exact ⟨minimum, Nat.lt_of_le_of_lt le
    (Nat.lt_trans (Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) h.memoryBound) (by decide))⟩

theorem Ready.of_keeps {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.FillContext.Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.X86_64.FillContext.Ready p pass lane slice index old t := by
  have bp := k.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp (k.regs .rsp (by decide)) base work k.rd k.wr,
    h.cache.of_keeps k, ?_, h.position.of_keeps k, ?_⟩
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

theorem finished_context {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : VG.Proof.Argon2.X86_64.FillContext.Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    ∃ old, VG.Proof.Argon2.X86_64.FillContext.Ready p pass lane slice p.segmentLen old t := by
  obtain ⟨old, cache⟩ := h.cache
  exact ⟨old, parameters, h.layout, cache, h.matrixWork, h.position, h.lanesWord⟩

end VG.Proof.Argon2.X86_64.FillContext
end

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice := by
  unfold VG.Proof.Argon2.X86_64.SegmentSetup.start; split <;> omega

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice ≤ g := by
  unfold VG.Proof.Argon2.X86_64.SegmentSetup.start; split <;> omega

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8) :
    WP isa (.block first) s fun t =>
      t.zf = decide (s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 = 0#64 ∧ s.gpr .r14 = 0#64) ∧
      Divide.Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [first, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change ((s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 ||| s.gpr .r14) - 0#64 == 0#64) = _
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : BitVec 32) :
    WP isa (.block [.mov register (.imm value)]) s fun t =>
      t.gpr register = value.signExtend 64 ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8)
    (passWord : s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) ∧ Divide.Keeps [.rcx, .r15] s t := by
  unfold index
  refine WP.seq ((VG.Proof.Argon2.X86_64.SegmentSetup.first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : a.zf = decide (pass = 0 ∧ slice = 0) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) (by simp only [eval, firstFlag]) ?_ ?_
  · intro mode
    refine (VG.Proof.Argon2.X86_64.SegmentSetup.register_ok a .r15 2).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold VG.Proof.Argon2.X86_64.SegmentSetup.start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (VG.Proof.Argon2.X86_64.SegmentSetup.register_ok a .r15 0).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold VG.Proof.Argon2.X86_64.SegmentSetup.start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State) : WP isa (.block check) s fun t =>
    t.cf = decide ((s.gpr .r15).toNat < (s.gpr .r13).toNat) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [check, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.cf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupReset`. -/
section
/-! Merged from `Proof.Argon2.X86_64.SegmentSetupReady`. -/
section
/-! Segment setup needs no previously valid cached block. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 8
  write : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.of_state {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.rbp, .rsp, .rbx, .r12, .r13, .r14], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .r12 (by simp)).trans h.laneLength, (regs .r13 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, (regs .rbx (by simp)).trans words.laneWord,
      (regs .r14 (by simp)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem Ready.saved {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s) (saved : AddressCache.Saved s t) : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice t := by
  have bp := congrFun saved.regs Reg.rbp
  have sp := congrFun saved.regs Reg.rsp
  have base : FillKernel.matrix t = FillKernel.matrix s := saved.read 232 (by decide) (by decide)
  refine ⟨h.parameters, h.layout.of_preserved bp sp base saved.work_eq saved.rd saved.wr,
    saved.ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved.rd, saved.wr, bp]; exact h.reads
  · rw [saved.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    exact ⟨(s.gpr .rax).toNat, saved.words words (by simp)⟩
  · rw [base, saved.work_eq]; exact h.matrixWork
  · rw [saved.regs]; exact h.laneLength
  · rw [saved.regs]; exact h.segmentLength
  · exact (saved.read 184 (by decide) (by decide)).trans h.lanesWord

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Reset the counter while preserving the segment header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Reset (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) : Prop where
  ready : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice t
  words : AddressHeader.Words p pass lane slice 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem reset_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (h : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s) :
    WP isa VG.Impl.Argon2.X86_64.SegmentSetup.reset s (VG.Proof.Argon2.X86_64.SegmentSetup.Reset s · p pass lane slice) := by
  unfold VG.Impl.Argon2.X86_64.SegmentSetup.reset
  refine WP.seq ((VG.Proof.Argon2.X86_64.SegmentSetup.register_ok s .rax 0).mono ?_)
  rintro a ⟨value, keeps⟩
  have next := h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  refine (AddressCache.save_ready a next.addressLayout next.write).mono ?_
  intro t saved
  obtain ⟨old, words⟩ := next.words
  have matrixA : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have workA : AddressCalls.work a = AddressCalls.work s := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .rbp (by decide)]
  refine ⟨next.saved saved, saved.words words value,
    (saved.read 232 (by decide) (by decide)).trans matrixA, saved.work_eq.trans workA,
    ?_, saved.rd.trans keeps.rd, saved.wr.trans keeps.wr, ?_, saved.mxcsr.trans keeps.mxcsr⟩
  · intro r hr
    have ne : r ∉ [Reg.rax] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (congrFun saved.regs r).trans (keeps.regs r ne)
  · have frame := saved.frame
    rw [keeps.mem, keeps.regs .rbp (by decide)] at frame
    exact frame

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! The prepared context covers ordinary and empty first-segment suffixes. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Prepared (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) : Prop where
  context : FillContext.Ready p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem prepare_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (h : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s) :
    WP isa VG.Impl.Argon2.X86_64.SegmentSetup.prepare s (VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s · p pass lane slice) := by
  unfold VG.Impl.Argon2.X86_64.SegmentSetup.prepare
  refine WP.seq ((VG.Proof.Argon2.X86_64.SegmentSetup.reset_ok s p pass lane slice h).mono ?_)
  intro a reset
  refine (VG.Proof.Argon2.X86_64.SegmentSetup.index_ok a pass slice (reset.ready.reads 0 (by simp)) reset.words.passWord reset.words.sliceWord
    (Nat.lt_trans h.parameters.passBound (by decide))
    (Nat.lt_trans h.parameters.sliceBound (by decide))).mono ?_
  rintro t ⟨value, keeps⟩
  have core := reset.ready.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  have cacheA : AddressCache.Invariant p pass lane slice 0 a :=
    ⟨reset.ready.addressLayout, reset.ready.reads, reset.ready.write, reset.words, by decide, Or.inl rfl⟩
  have cache := cacheA.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  have base : FillKernel.matrix t = FillKernel.matrix a := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have work : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .rbp (by decide)]
  refine ⟨⟨core.parameters, core.layout, cache, core.matrixWork,
    ⟨cache.words.laneWord, core.laneLength, core.segmentLength, cache.words.sliceWord, value⟩, core.lanesWord⟩,
    base.trans reset.matrix, work.trans reset.work, ?_, keeps.rd.trans reset.rd,
    keeps.wr.trans reset.wr, ?_, keeps.mxcsr.trans reset.mxcsr⟩
  · intro r hr ne
    have outside : r ∉ [Reg.rcx, .r15] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reset.regs r hr)
  · rw [keeps.mem]; exact reset.frame

theorem Prepared.represents {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s t : State}
    (ready : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s) (h : VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s t p pass lane slice) (blocks : Array VG.Spec.Argon2.Block)
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

end VG.Proof.Argon2.X86_64.SegmentSetup

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup`. -/
section

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupCheck`. -/
section
/-! Check the prepared index before entering the nonempty segment loop. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

theorem Prepared.of_keeps {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s a t : State}
    (h : VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s a p pass lane slice) (k : Divide.Keeps [] a t) : VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s t p pass lane slice := by
  have bp := k.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.context.of_keeps (k.mono (by decide)), base.trans h.matrix, work.trans h.work,
    ?_, k.rd.trans h.rd, k.wr.trans h.wr, ?_, k.mxcsr.trans h.mxcsr⟩
  · intro r hr ne; exact (k.regs r (by simp)).trans (h.regs r hr ne)
  · rw [k.mem]; exact h.frame

theorem check_prepared_ok {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s a : State}
    (h : VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s a p pass lane slice) : WP isa (.block check) a fun t =>
      VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s t p pass lane slice ∧ t.cf = decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen) := by
  refine (VG.Proof.Argon2.X86_64.SegmentSetup.check_ok a).mono ?_
  rintro t ⟨flag, keeps⟩
  have minimum := h.context.parameters.segment_bound
  refine ⟨h.of_keeps keeps, ?_⟩
  rw [flag, h.context.position.index, h.context.position.segmentLength,
    ReferenceMap.word_nat (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) (Nat.lt_of_le_of_lt (VG.Proof.Argon2.X86_64.SegmentSetup.start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem finished_prepared {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s a t : State} {state : FillState}
    (prepared : VG.Proof.Argon2.X86_64.SegmentSetup.Prepared s a p pass lane slice) (finished : FillSegment.Finished a t p pass lane slice state) :
    FillSegment.Finished s t p pass lane slice state := by
  refine ⟨finished.represented, finished.matrix.trans prepared.matrix, finished.work.trans prepared.work,
    finished.position, finished.layout, finished.cache, finished.matrixWork, finished.passWord, finished.lanesWord,
    ?_, finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.mxcsr.trans (ctl_eq_of prepared.mxcsr)⟩
  · intro r hr ne; exact (finished.regs r hr ne).trans (prepared.regs r hr ne)
  · have firstFrame : Frame (FillBlock.writes s p) s.mem a.mem := by
      apply prepared.frame.sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8, 16⟩, by simp [FillBlock.writes], Region.sub_prefix (by decide)⟩
    have rest := finished.frame
    rw [FillBlock.writes, prepared.matrix, prepared.work,
      prepared.regs .rsp (by simp [calleeSaved]) (by decide),
      prepared.regs .rbp (by simp [calleeSaved]) (by decide)] at rest
    exact firstFrame.trans rest

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Fill one complete segment, including the initialized prefix and empty suffix. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

theorem code_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat)
    (h : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa VG.Impl.Argon2.X86_64.SegmentSetup.code s (FillSegment.Finished s · p pass lane slice
      (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state)) := by
  rw [Proof.Argon2.segment_start p pass lane slice state h.parameters.segment_bound.1]
  change WP isa VG.Impl.Argon2.X86_64.SegmentSetup.code s (FillSegment.Finished s · p pass lane slice
    (Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) state))
  unfold VG.Impl.Argon2.X86_64.SegmentSetup.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.SegmentSetup.prepare_ok s p pass lane slice h).mono ?_)
  intro a prepared
  refine WP.seq ((VG.Proof.Argon2.X86_64.SegmentSetup.check_prepared_ok prepared).mono ?_)
  rintro b ⟨prepared, flag⟩
  have matrix := prepared.represents h state.memory represented
  refine WP.ite (decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen)) (by simp only [eval, flag]) ?_ ?_
  · intro taken
    have bound := of_decide_eq_true taken
    have active := prepared.context.activate bound (VG.Proof.Argon2.X86_64.SegmentSetup.start_active pass slice)
    refine (FillSegment.loop_ok (p.segmentLen - VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) b p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0
      active state matrix (by omega) (by omega)).mono ?_
    intro t finished
    exact VG.Proof.Argon2.X86_64.SegmentSetup.finished_prepared prepared finished
  · intro skipped
    have bound := of_decide_eq_false skipped
    have minimum := h.parameters.segment_bound.1
    have last : VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice = p.segmentLen := by have := VG.Proof.Argon2.X86_64.SegmentSetup.start_le pass slice p.segmentLen minimum; omega
    have finished : FillSegment.Finished b b p pass lane slice state :=
      ⟨matrix, rfl, rfl, last ▸ prepared.context.position, prepared.context.layout,
        ⟨0, prepared.context.cache⟩, prepared.context.matrixWork, prepared.context.cache.words.passWord,
        prepared.context.lanesWord, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
    rw [last, Nat.sub_self, Proof.Argon2.segment_zero]
    exact WP.block_nil (VG.Proof.Argon2.X86_64.SegmentSetup.finished_prepared prepared finished)

end VG.Proof.Argon2.X86_64.SegmentSetup

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance`. -/
section

/-! Lane advancement retains the allocation and public segment parameters. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillLanes

theorem advance_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 184) 8) :
    WP isa (.block VG.Impl.Argon2.X86_64.FillLanes.advance) s fun t => t.gpr .rbx = s.gpr .rbx + 1 ∧
      t.cf = decide ((s.gpr .rbx + 1).toNat < (s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 184) 64).toNat) ∧
      Divide.Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.FillLanes.advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, VG.Proof.Argon2.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, hr,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem context_ready {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s : State}
    (h : FillContext.Ready p pass lane slice index old s) : SegmentSetup.Ready p pass lane slice s :=
  ⟨h.parameters, h.layout, h.cache.layout, h.cache.reads, h.cache.write, ⟨old, h.cache.words⟩,
    h.matrixWork, h.position.laneLength, h.position.segmentLength, h.lanesWord⟩

theorem finished_ready {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : FillContext.Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    SegmentSetup.Ready p pass lane slice t := by
  obtain ⟨old, context⟩ := FillContext.finished_context parameters h
  exact VG.Proof.Argon2.X86_64.FillLanes.context_ready context

theorem change_lane_ready {p : VG.Spec.Argon2.Params} {pass lane slice newLane : Nat} {s t : State}
    (h : SegmentSetup.Ready p pass lane slice s) (k : Divide.Keeps [.rbx] s t)
    (value : t.gpr .rbx = BitVec.ofNat 64 newLane) (active : newLane < p.lanes) :
    SegmentSetup.Ready p pass newLane slice t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨{ h.parameters with laneBound := active }, h.layout.of_preserved bp sp base work k.rd k.wr,
    ?_, ?_, ?_, ?_, ?_, (k.regs .r12 (by decide)).trans h.laneLength,
    (k.regs .r13 (by decide)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [k.rd, k.wr, bp]; exact h.addressLayout.frameRead
    · rw [k.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [k.rd, k.wr, bp]; exact h.reads
  · rw [k.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, value, (k.regs .r14 (by decide)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [k.mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

end VG.Proof.Argon2.X86_64.FillLanes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillLanesBody`. -/
section

/-! One lane iteration fills its segment and advances the public lane. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 (lane + 1)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r15 → t.gpr r = s.gpr r
  header : ∃ a, SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.rbx] a t
  cf : t.cf = decide (lane + 1 < p.lanes)
  next : lane + 1 < p.lanes → SegmentSetup.Ready p pass (lane + 1) slice t

theorem body_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillLanes.body s (VG.Proof.Argon2.X86_64.FillLanes.Done s · p pass lane slice state) := by
  unfold Impl.Argon2.X86_64.FillLanes.body
  refine WP.seq ((SegmentSetup.code_ok s p pass lane slice h state represented).mono ?_)
  intro a filled
  have ready := VG.Proof.Argon2.X86_64.FillLanes.finished_ready h.parameters filled
  refine (VG.Proof.Argon2.X86_64.FillLanes.advance_ok a (ready.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨value, flag, keeps⟩
  obtain ⟨old, words⟩ := ready.words
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have added : a.gpr .rbx + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [words.laneWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans h.parameters.lanesBound (by decide)
  have laneBound := h.parameters.laneBound
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextWord, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, (ctl_eq_of keeps.mxcsr).trans filled.mxcsr, ?_, ⟨a, ready, keeps⟩, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx ix
    have outside : r ∉ [Reg.rbx] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (keeps.regs r outside).trans (filled.regs r hr ix)
  · rw [flag, added, ready.lanesWord, ReferenceMap.word_nat (lane + 1) (by omega),
      ReferenceMap.word_nat p.lanes lanesBound]
  · intro active; exact VG.Proof.Argon2.X86_64.FillLanes.change_lane_ready ready keeps nextWord active

end VG.Proof.Argon2.X86_64.FillLanes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillLanes`. -/
section

/-! Termination and correctness of all remaining lanes in one slice. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r15 → t.gpr r = s.gpr r
  header : ∃ lane a, lane + 1 = p.lanes ∧ SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.rbx] a t

theorem Done.finished {s t : State} {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {state : FillState}
    (h : VG.Proof.Argon2.X86_64.FillLanes.Done s t p pass lane slice state) (last : lane + 1 = p.lanes) :
    VG.Proof.Argon2.X86_64.FillLanes.Finished s t p pass slice (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) := by
  obtain ⟨a, ready, keeps⟩ := h.header
  exact ⟨h.represented, h.matrix, h.work, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr,
    h.regs, lane, a, last, ready, keeps⟩

theorem Finished.prepend {s a t : State} {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {state finalState : FillState}
    (first : VG.Proof.Argon2.X86_64.FillLanes.Done s a p pass lane slice state) (rest : VG.Proof.Argon2.X86_64.FillLanes.Finished a t p pass slice finalState) :
    VG.Proof.Argon2.X86_64.FillLanes.Finished s t p pass slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_, rest.header⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx ix; exact (rest.regs r hr bx ix).trans (first.regs r hr bx ix)

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.FillLanes.loop s
      (VG.Proof.Argon2.X86_64.FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice lane count state)) := by
  induction count generalizing s lane state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.X86_64.FillLanes.body_ok s p pass lane slice h state represented
    rw [Proof.Argon2.lanes_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.FillLanes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillSlice`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillSlicePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillHeader`. -/
section
/-! Allocation and normalized header across lane, slice and pass boundaries. -/

namespace VG.Proof.Argon2.X86_64.FillHeader

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (s : State) : Prop where
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 8
  write : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem of_segment_ready {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s : State}
    (h : SegmentSetup.Ready p pass lane slice s) : VG.Proof.Argon2.X86_64.FillHeader.Ready p pass lane slice s :=
  ⟨h.layout, h.addressLayout, h.reads, h.write, h.words, h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.segment {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s : State}
    (h : VG.Proof.Argon2.X86_64.FillHeader.Ready p pass lane slice s) (parameters : FillContext.Parameters p pass lane slice) :
    SegmentSetup.Ready p pass lane slice s :=
  ⟨parameters, h.layout, h.addressLayout, h.reads, h.write, h.words,
    h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.of_state {p : VG.Spec.Argon2.Params} {pass lane slice newLane newSlice : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.FillHeader.Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.rbp, .rsp, .r12, .r13], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (laneWord : t.gpr .rbx = BitVec.ofNat 64 newLane) (sliceWord : t.gpr .r14 = BitVec.ofNat 64 newSlice) :
    VG.Proof.Argon2.X86_64.FillHeader.Ready p pass newLane newSlice t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .r12 (by simp)).trans h.laneLength, (regs .r13 (by simp)).trans h.segmentLength, ?_⟩
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

theorem of_lanes_finished {p : VG.Spec.Argon2.Params} {pass slice : Nat} {s t : State} {state : FillState}
    (h : FillLanes.Finished s t p pass slice state) : VG.Proof.Argon2.X86_64.FillHeader.Ready p pass p.lanes slice t := by
  obtain ⟨lane, a, _, ready, keeps⟩ := h.header
  obtain ⟨old, words⟩ := ready.words
  apply (VG.Proof.Argon2.X86_64.FillHeader.of_segment_ready ready).of_state _ keeps.mem keeps.rd keeps.wr h.laneWord
    ((keeps.regs .r14 (by decide)).trans words.sliceWord)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)

end VG.Proof.Argon2.X86_64.FillHeader
end

/-! Initialize lane zero without requiring a valid incoming lane coordinate. -/

namespace VG.Proof.Argon2.X86_64.FillSlice

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : VG.Spec.Argon2.Params) (pass slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 slice
  header : ∃ lane, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat) : Prop where
  ready : SegmentSetup.Ready p pass 0 slice t
  keeps : Divide.Keeps [.rbx] s t

theorem setup_ok (s : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat) (h : VG.Proof.Argon2.X86_64.FillSlice.Ready p pass slice s) :
    WP isa (.block Impl.Argon2.X86_64.FillSlice.setup) s (VG.Proof.Argon2.X86_64.FillSlice.Prepared s · p pass slice) := by
  refine (SegmentSetup.register_ok s .rbx 0).mono ?_
  rintro t ⟨laneWord, keeps⟩
  obtain ⟨lane, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass 0 slice t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.mem keeps.rd keeps.wr laneWord ((keeps.regs .r14 (by decide)).trans words.sliceWord)
  exact ⟨next.segment h.parameters, keeps⟩

end VG.Proof.Argon2.X86_64.FillSlice
end

/-! Correctness of one complete slice, starting at lane zero. -/

namespace VG.Proof.Argon2.X86_64.FillSlice

open VG VG.X86_64 VG.Spec.Argon2

theorem code_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat) (h : VG.Proof.Argon2.X86_64.FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlice.code s
      (FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice 0 p.lanes state)) := by
  unfold Impl.Argon2.X86_64.FillSlice.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillSlice.setup_ok s p pass slice h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .rbp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillLanes.loop_ok p.lanes a p pass 0 slice prepared.ready state representedA
    h.parameters.lanesPositive (by omega)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.laneWord,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.mxcsr.trans (ctl_eq_of prepared.keeps.mxcsr), ?_, finished.header⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.regs .rsp (by decide), bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx ix
    have ne : r ∉ [Reg.rbx] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (finished.regs r hr bx ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.X86_64.FillSlice

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillSlicesBody`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillSliceAdvance`. -/
section
/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSlices

theorem advance_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.FillSlices.advance) s fun t =>
    t.gpr .r14 = s.gpr .r14 + 1 ∧ t.cf = decide ((s.gpr .r14 + 1).toNat < 4) ∧ Divide.Keeps [.r14] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.FillSlices.advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (4 : BitVec 32) = (4 : Addr) from rfl,
    show (4 : Addr).toNat = 4 from rfl,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem advanced_header {s t : State} {p : VG.Spec.Argon2.Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.r14] s t)
    (value : t.gpr .r14 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.mem k.rd k.wr ((k.regs .rbx (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.X86_64.FillSlices
end

/-! Fill one slice and advance its public coordinate. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.lanes p pass slice 0 p.lanes state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes (slice + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  cf : t.cf = decide (slice + 1 < 4)
  next : slice + 1 < 4 → FillSlice.Ready p pass (slice + 1) t

theorem body_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat) (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlices.body s (VG.Proof.Argon2.X86_64.FillSlices.Done s · p pass slice state) := by
  unfold Impl.Argon2.X86_64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  refine (VG.Proof.Argon2.X86_64.FillSlices.advance_ok a).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : a.gpr .r14 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  have nextHeader := VG.Proof.Argon2.X86_64.FillSlices.advanced_header header keeps nextWord
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have sliceBound := h.parameters.sliceBound
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextHeader, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, (ctl_eq_of keeps.mxcsr).trans filled.mxcsr, ?_, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx sl ix
    have outside : r ∉ [Reg.r14] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (keeps.regs r outside).trans (filled.regs r hr bx ix)
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega)]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.X86_64.FillSlices

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillSlices`. -/
section

/-! Termination and correctness of the four-slice filling pass. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : VG.Spec.Argon2.Params} {pass slice : Nat} {state : FillState}
    (h : VG.Proof.Argon2.X86_64.FillSlices.Done s t p pass slice state) (last : slice + 1 = 4) :
    VG.Proof.Argon2.X86_64.FillSlices.Finished s t p pass (Proof.Argon2.lanes p pass slice 0 p.lanes state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : VG.Spec.Argon2.Params} {pass slice : Nat} {state finalState : FillState}
    (first : VG.Proof.Argon2.X86_64.FillSlices.Done s a p pass slice state) (rest : VG.Proof.Argon2.X86_64.FillSlices.Finished a t p pass finalState) : VG.Proof.Argon2.X86_64.FillSlices.Finished s t p pass finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : VG.Spec.Argon2.Params) (pass slice : Nat)
    (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    WP isa Impl.Argon2.X86_64.FillSlices.loop s (VG.Proof.Argon2.X86_64.FillSlices.Finished s · p pass (Proof.Argon2.slices p pass slice count state)) := by
  induction count generalizing s slice state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.X86_64.FillSlices.body_ok s p pass slice h state represented
    rw [Proof.Argon2.slices_succ]
    cases n with
    | zero =>
      have last : slice + 1 = 4 := endSlice
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : slice + 1 < 4 := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (slice + 1) (done.next active)
        (Proof.Argon2.lanes p pass slice 0 p.lanes state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

theorem pass_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (h : FillSlice.Ready p pass 0 s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlices.loop s (VG.Proof.Argon2.X86_64.FillSlices.Finished s · p pass (fillPass p state pass)) := by
  rw [← Proof.Argon2.slices_pass p pass state]
  exact VG.Proof.Argon2.X86_64.FillSlices.loop_ok 4 s p pass 0 h state represented (by decide) (by decide)

end VG.Proof.Argon2.X86_64.FillSlices

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillIteration`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillIterationPrepare`. -/
section
/-! Start a pass at slice zero regardless of its incoming lane and slice coordinates. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : VG.Spec.Argon2.Params) (pass : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 0
  header : ∃ lane slice, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : VG.Spec.Argon2.Params) (pass : Nat) : Prop where
  ready : FillSlice.Ready p pass 0 t
  keeps : Divide.Keeps [.r14] s t

theorem setup_ok (s : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (h : VG.Proof.Argon2.X86_64.FillIteration.Ready p pass s) :
    WP isa (.block Impl.Argon2.X86_64.FillIteration.setup) s (VG.Proof.Argon2.X86_64.FillIteration.Prepared s · p pass) := by
  refine (SegmentSetup.register_ok s .r14 0).mono ?_
  rintro t ⟨sliceWord, keeps⟩
  obtain ⟨lane, slice, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass lane 0 t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.mem keeps.rd keeps.wr ((keeps.regs .rbx (by decide)).trans words.laneWord) sliceWord
  exact ⟨⟨h.parameters, lane, next⟩, keeps⟩

end VG.Proof.Argon2.X86_64.FillIteration
end

/-! One complete filling pass against the reviewed specification. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

theorem code_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (h : VG.Proof.Argon2.X86_64.FillIteration.Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.X86_64.FillIteration.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillIteration.setup_ok s p pass h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .rbp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillSlices.pass_ok a p pass prepared.ready state representedA).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.header,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.mxcsr.trans (ctl_eq_of prepared.keeps.mxcsr), ?_⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.regs .rsp (by decide), bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.r14] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (finished.regs r hr bx sl ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.X86_64.FillIteration

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillIterationsBody`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillPassSave`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPassCounter`. -/
section
/-! Increment, save and compare the public pass counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .rax = s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 + 1 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [increment, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 72) 8) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      t.cf = decide ((s.gpr .rax).toNat < (s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 72) 64).toNat) := by
  apply WP.of_runBlock
  have sep : Mem.Sep (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 72) 8 (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  simp only [saveCheck, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.load64, VG.Proof.Argon2.X86_64.ea_at, hw, hr, readSrc, execAlu, ite_true,
    Mem.readW_writeW_sep (w := 64) (w' := 64) sep (by decide), RegUpd.cf_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, trivial⟩
  rfl

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! A saved pass counter changes only its eight-byte header word. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) (s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 + 1)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  cf : t.cf = decide ((s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 + 1).toNat <
    (s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 72) 64).toNat)
  frame : Frame [⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0, 8⟩] s.mem t.mem

theorem advance_ok (s : State) (read : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8)
    (write : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8)
    (passesRead : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 72) 8) : WP isa VG.Impl.Argon2.X86_64.FillIterations.advance s (VG.Proof.Argon2.X86_64.FillIterations.Saved s) := by
  unfold VG.Impl.Argon2.X86_64.FillIterations.advance
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillIterations.increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have readA : InRegions (a.rd ++ a.wr) (VG.Proof.Argon2.X86_64.off (a.gpr .rbp) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (VG.Proof.Argon2.X86_64.off (a.gpr .rbp) 0) 8 := by rw [keeps.wr, bp]; exact write
  refine (VG.Proof.Argon2.X86_64.FillIterations.saveCheck_ok a writeA readA).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx, cf⟩
  have finalMem : t.mem = s.mem.writeW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) (s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 64 + 1) := by
    rw [mem, keeps.mem, bp, value]
  refine ⟨finalMem, ?_, rd.trans keeps.rd, wr.trans keeps.wr, ctl_eq_of (mx.trans keeps.mxcsr), ?_, ?_⟩
  · intro r ne
    have outside : r ∉ [Reg.rax] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne
    exact (congrFun regs r).trans (keeps.regs r outside)
  · rw [cf, value, keeps.mem, bp]
  · rw [finalMem]
    exact (Frame.refl _ _).writeW (r := ⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0, 8⟩) (by simp) _ (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : VG.Proof.Argon2.X86_64.FillIterations.Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) d) 64 = s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 64 := by
  rw [h.regs .rbp (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega) (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : VG.Spec.Argon2.Params} {pass lane slice old : Nat}
    (h : VG.Proof.Argon2.X86_64.FillIterations.Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
    AddressHeader.Words p (pass + 1) lane slice old t := by
  refine ⟨?_, (h.regs .rbx (by decide)).trans words.laneWord,
    (h.regs .r14 (by decide)).trans words.sliceWord,
    (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord,
    (h.read 8 (by decide) (by decide)).trans words.counterWord⟩
  rw [h.regs .rbp (by decide), h.mem, Mem.readW_writeW_self64, words.passWord, BitVec.ofNat_add]
  rfl

theorem Saved.header {s t : State} {p : VG.Spec.Argon2.Params} {pass lane slice : Nat}
    (h : VG.Proof.Argon2.X86_64.FillIterations.Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
  have bp := h.regs .rbp (by decide)
  have sp := h.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := h.read 248 (by decide) (by decide)
  refine ⟨header.layout.of_preserved bp sp base work h.rd h.wr, ?_, ?_, ?_, ?_, ?_,
    (h.regs .r12 (by decide)).trans header.laneLength, (h.regs .r13 (by decide)).trans header.segmentLength, ?_⟩
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

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! Merged from `Proof.Argon2.X86_64.FillIterationsFrame`. -/
section
/-! The outer pass loop also writes the public pass word at frame offset zero. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : VG.Spec.Argon2.Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.gpr .rsp) 8, ⟨s.gpr .rbp, 24⟩]

theorem filling_frame {s t : State} {p : VG.Spec.Argon2.Params} (h : Frame (FillBlock.writes s p) s.mem t.mem) :
    Frame (VG.Proof.Argon2.X86_64.FillIterations.writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillIterations.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillIterations.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillIterations.writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rbp, 24⟩, by simp [VG.Proof.Argon2.X86_64.FillIterations.writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : VG.Spec.Argon2.Params} (h : VG.Proof.Argon2.X86_64.FillIterations.Saved s t) : Frame (VG.Proof.Argon2.X86_64.FillIterations.writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .rbp, 24⟩, by simp [VG.Proof.Argon2.X86_64.FillIterations.writes], Offset.sub_base _ (by decide)⟩

theorem Saved.represents {s t : State} {p : VG.Spec.Argon2.Params} {pass lane slice : Nat}
    (h : VG.Proof.Argon2.X86_64.FillIterations.Saved s t) (header : FillHeader.Ready p pass lane slice s) (blocks : Array VG.Spec.Argon2.Block)
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

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : VG.Spec.Argon2.Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 0) 8

structure Done (s t : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillIterations.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  cf : t.cf = decide (pass + 1 < p.passes)
  next : pass + 1 < p.passes → VG.Proof.Argon2.X86_64.FillIterations.Ready p (pass + 1) t

theorem body_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (h : VG.Proof.Argon2.X86_64.FillIterations.Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillIterations.body s (VG.Proof.Argon2.X86_64.FillIterations.Done s · p pass state) := by
  unfold Impl.Argon2.X86_64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (VG.Proof.Argon2.X86_64.off (a.gpr .rbp) 0) 8 := by
    rw [filled.wr, filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  refine (VG.Proof.Argon2.X86_64.FillIterations.advance_ok a (filled.header.reads 0 (by simp)) write (filled.header.reads 72 (by simp))).mono ?_
  intro t saved
  have header := saved.header filled.header
  obtain ⟨old, words⟩ := filled.header.words
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  have passBound := h.filling.parameters.passBound
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.mxcsr.trans filled.mxcsr, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [VG.Proof.Argon2.X86_64.FillIterations.writes, filled.matrix, filled.work,
      filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at lastFrame
    exact (VG.Proof.Argon2.X86_64.FillIterations.filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
      rw [BitVec.ofNat_add]; rfl
    rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .rbp (by decide)]; exact write

end VG.Proof.Argon2.X86_64.FillIterations

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillIterations`. -/
section

/-! Termination and correctness of every requested filling pass. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : VG.Spec.Argon2.Params) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p p.passes p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillIterations.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : VG.Spec.Argon2.Params} {pass : Nat} {state : FillState}
    (h : VG.Proof.Argon2.X86_64.FillIterations.Done s t p pass state) (last : pass + 1 = p.passes) : VG.Proof.Argon2.X86_64.FillIterations.Finished s t p (fillPass p state pass) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : VG.Spec.Argon2.Params} {pass : Nat} {state finalState : FillState}
    (first : VG.Proof.Argon2.X86_64.FillIterations.Done s a p pass state) (rest : VG.Proof.Argon2.X86_64.FillIterations.Finished a t p finalState) : VG.Proof.Argon2.X86_64.FillIterations.Finished s t p finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [VG.Proof.Argon2.X86_64.FillIterations.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : VG.Spec.Argon2.Params) (pass : Nat) (h : VG.Proof.Argon2.X86_64.FillIterations.Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    WP isa Impl.Argon2.X86_64.FillIterations.loop s (VG.Proof.Argon2.X86_64.FillIterations.Finished s · p (Proof.Argon2.iterations p pass count state)) := by
  induction count generalizing s pass state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.X86_64.FillIterations.body_ok s p pass h state represented
    rw [Proof.Argon2.iterations_succ]
    cases n with
    | zero =>
      have last : pass + 1 = p.passes := endPass
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : pass + 1 < p.passes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (pass + 1) (done.next active)
        (fillPass p state pass) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

theorem Finished.frame_word {s t : State} {p : VG.Spec.Argon2.Params} {pass : Nat} {state : FillState}
    (ready : VG.Proof.Argon2.X86_64.FillIterations.Ready p pass s) (done : VG.Proof.Argon2.X86_64.FillIterations.Finished s t p state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : 24 ≤ d) :
    t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) d) 64 = s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)]
  obtain ⟨lane, slice, header⟩ := ready.filling.header
  have sub : Region.Sub ⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.FillIterations.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact header.layout.matrixFrame.symm.sub_left sub
    · exact header.addressLayout.frameWork.sub_left sub
    · exact header.addressLayout.frameStack.sub_left sub
    · simpa only [VG.Proof.Argon2.X86_64.off, BitVec.add_zero] using Offset.disjoint (d := d) (n := 8) (e := 0) (k := 24) (s.gpr .rbp) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.FillIterations

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitCall`. -/
section

/-! # A verified H′ call to initialize a memory block -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v)) := by
  have all (c : Prog isa) (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi; simp only [h i hi, Bool.not_false]
  have hi := all _ (HPrime.hash_ok v).initNoSp
  have hu := all _ (HPrime.hash_ok v).updateNoSp
  have hf := all _ (HPrime.hash_ok v).finalizeNoSp
  have check : (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v)).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    simp only [VG.Impl.Argon2.X86_64.HPrime.code, VG.Impl.Argon2.X86_64.HPrime.setup, VG.Impl.Argon2.X86_64.HPrime.saved, VG.Impl.Argon2.X86_64.HPrime.first, chooseLength, init, initArgs, absorbFixed,
      fixedArgs, VG.Impl.Argon2.X86_64.HPrime.update, updateArgs, absorbInput, inputArgs, finishInput, finalize,
      finalizeArgs, finishOutput, extendDigest, emitPrefix, copy, copyByte, chain,
      next, copyRemaining, restore, Code.allInstrs]
    rw [hi, hu, hf]
    decide +kernel
  rw [Code.allInstrs_eq, List.all_eq_true] at check
  intro i hi
  simpa only [Bool.not_eq_true'] using check i hi

theorem hPrime_depth (v : Proof.Blake2.X86_64.Backend) : (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v)).depth = 2 := by
  simp only [VG.Impl.Argon2.X86_64.HPrime.code, VG.Impl.Argon2.X86_64.HPrime.first, chooseLength, init, absorbFixed, VG.Impl.Argon2.X86_64.HPrime.update, absorbInput,
    finishInput, finalize, finishOutput, extendDigest, emitPrefix, copy, chain,
    next, copyRemaining, Code.depth, (HPrime.hash_ok v).initDepth,
    (HPrime.hash_ok v).updateDepth, (HPrime.hash_ok v).finalizeDepth]
  rfl

structure CallReady (s : State) : Prop where
  input : Covers [⟨s.gpr .rdi, 72⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, 1024⟩] s.wr
  work : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .rdi, 72⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  outputWork : (⟨s.gpr .rdx, 1024⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 72⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 1024⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r8, 16384⟩

structure Called (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .rdx) 1024 = Spec.Argon2.hPrime 1024 (bytesAt s.mem (s.gpr .rdi) 72)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem hPrime_call_hyps (s : State) (h : VG.Proof.Argon2.X86_64.MemoryInit.CallReady s)
    (inputLength : s.gpr .rsi = 72) (outputLength : s.gpr .rcx = 1024) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 72⟩]
      [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩]) ∧
    Covers [⟨s.gpr .rdi, 72⟩, ⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩] s.wr := by
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have inner := below_callee (s.gpr .rsp) 16
  have ret := below_sub (sp := s.gpr .rsp) (by decide : 8 ≤ 24) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, HPrime.retR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_rsp, inputLength, outputLength]
    exact ⟨rfl, rfl, by decide, by decide, by decide, h.inputWork, h.outputWork,
      h.stackInput.sub_left inner, h.stackOutput.sub_left inner, h.stackWork.sub_left inner,
      h.stackOutput.sub_left ret, h.stackWork.sub_left ret⟩
  · intro p n hp
    rcases hp with ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · exact ⟨_, List.mem_append_right _ h.work, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, h.work, hc⟩

theorem hPrime_call_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (h : VG.Proof.Argon2.X86_64.MemoryInit.CallReady s) (inputLength : s.gpr .rsi = 72)
    (outputLength : s.gpr .rcx = 1024) :
    WP isa (.call name (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v))) s (VG.Proof.Argon2.X86_64.MemoryInit.Called s) := by
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.X86_64.MemoryInit.hPrime_call_hyps s h inputLength outputLength
  refine WP.call (k := HPrime.localContract) (HPrime.code_correct v) (VG.Proof.Argon2.X86_64.MemoryInit.hPrime_nosp v)
    (by rw [VG.Proof.Argon2.X86_64.MemoryInit.hPrime_depth]; decide) pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, digest⟩
  have inputBytes : bytesAt s.callEntry.mem (s.gpr .rdi) 72 = bytesAt s.mem (s.gpr .rdi) 72 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact Proof.MdStream.X86_64.callEntry_byte s (h.stackInput.sub_left
      (below_sub (by decide) (by decide))) (show (72 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine ⟨?_, regs, rd, wr, ?_⟩
  · change bytesAt u.mem (s.callEntry.gpr .rdx) (s.callEntry.gpr .rcx).toNat =
      Spec.Argon2.hPrime (s.callEntry.gpr .rcx).toNat
        (bytesAt s.callEntry.mem (s.callEntry.gpr .rdi) (s.callEntry.gpr .rsi).toNat) at digest
    rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      memU, inputLength, outputLength,
      show (72 : Addr).toNat = 72 from rfl,
      show (1024 : Addr).toNat = 1024 from rfl, inputBytes] at digest
    exact digest
  · rw [VG.Proof.Argon2.X86_64.MemoryInit.hPrime_depth] at frame
    exact frame

end VG.Proof.Argon2.X86_64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FinalCall`. -/
section

/-! The final H′ call accepts a complete reduced block and a public tag length. -/

namespace VG.Proof.Argon2.X86_64.FinalCall

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (code)
open VG.Spec.Blake2 (bytesAt)

structure CallReady (len : Nat) (s : State) : Prop where
  positive : 1 ≤ len
  bound : len < 2 ^ 32
  input : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, len⟩] s.wr
  work : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  outputWork : (⟨s.gpr .rdx, len⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, len⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r8, 16384⟩

structure Called (len : Nat) (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .rdx) len = Spec.Argon2.hPrime len (bytesAt s.mem (s.gpr .rdi) 1024)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem hPrime_call_hyps (len : Nat) (s : State) (h : VG.Proof.Argon2.X86_64.FinalCall.CallReady len s)
    (inputLength : s.gpr .rsi = 1024) (outputLength : s.gpr .rcx = BitVec.ofNat 64 len) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 1024⟩]
      [⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩]) ∧
    Covers [⟨s.gpr .rdi, 1024⟩, ⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩] s.wr := by
  have length : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))]
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have inner := below_callee (s.gpr .rsp) 16
  have ret := below_sub (sp := s.gpr .rsp) (by decide : 8 ≤ 24) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, HPrime.retR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_rsp, inputLength, outputLength, length]
    exact ⟨rfl, trivial, by decide, h.positive, h.bound, h.inputWork, h.outputWork,
      h.stackInput.sub_left inner, h.stackOutput.sub_left inner, h.stackWork.sub_left inner,
      h.stackOutput.sub_left ret, h.stackWork.sub_left ret⟩
  · intro p n hp
    rcases hp with ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · exact ⟨_, List.mem_append_right _ h.work, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, h.work, hc⟩

theorem hPrime_call_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (len : Nat) (s : State) (h : VG.Proof.Argon2.X86_64.FinalCall.CallReady len s) (inputLength : s.gpr .rsi = 1024)
    (outputLength : s.gpr .rcx = BitVec.ofNat 64 len) :
    WP isa (.call name (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v))) s (VG.Proof.Argon2.X86_64.FinalCall.Called len s) := by
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.X86_64.FinalCall.hPrime_call_hyps len s h inputLength outputLength
  refine WP.call (k := HPrime.localContract) (HPrime.code_correct v) (MemoryInit.hPrime_nosp v)
    (by rw [MemoryInit.hPrime_depth]; decide) pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, digest⟩
  have inputBytes : bytesAt s.callEntry.mem (s.gpr .rdi) 1024 = bytesAt s.mem (s.gpr .rdi) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact Proof.MdStream.X86_64.callEntry_byte s (h.stackInput.sub_left
      (below_sub (by decide) (by decide))) (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine ⟨?_, regs, rd, wr, ?_⟩
  · change bytesAt u.mem (s.callEntry.gpr .rdx) (s.callEntry.gpr .rcx).toNat =
      Spec.Argon2.hPrime (s.callEntry.gpr .rcx).toNat
        (bytesAt s.callEntry.mem (s.callEntry.gpr .rdi) (s.callEntry.gpr .rsi).toNat) at digest
    rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      memU, inputLength, outputLength,
      show (1024 : Addr).toNat = 1024 from rfl,
      show (BitVec.ofNat 64 len).toNat = len from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))], inputBytes] at digest
    exact digest
  · rw [MemoryInit.hPrime_depth] at frame
    exact frame

end VG.Proof.Argon2.X86_64.FinalCall

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState`. -/
section

/-! Public loop metadata survives accumulator writes and register-only advancement. -/

namespace VG.Proof.Argon2.X86_64.ReductionState

open VG VG.X86_64 VG.Spec.Argon2

theorem Ready.of_state {p : VG.Spec.Argon2.Params} {s t : State} (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (length : t.gpr .r12 = s.gpr .r12)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.X86_64.ReductionState.Ready p t := by
  have base : VG.Proof.Argon2.X86_64.ReductionState.matrix t = VG.Proof.Argon2.X86_64.ReductionState.matrix s := by unfold VG.Proof.Argon2.X86_64.ReductionState.matrix; rw [mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, length.trans h.length⟩
  · rw [rd, wr, bp]; exact h.read
  · rw [base, wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_state {p : VG.Spec.Argon2.Params} {s t : State} {memory : Array VG.Spec.Argon2.Block} {acc : VG.Spec.Argon2.Block}
    (h : Represents p memory acc s) (bp : t.gpr .rbp = s.gpr .rbp) (mem : t.mem = s.mem) :
    Represents p memory acc t := by
  have base : VG.Proof.Argon2.X86_64.ReductionState.matrix t = VG.Proof.Argon2.X86_64.ReductionState.matrix s := by unfold VG.Proof.Argon2.X86_64.ReductionState.matrix; rw [mem, bp]
  constructor
  · rw [mem, base]; exact h.accumulator
  · rw [mem, base]; exact h.last

theorem frame_word {p : VG.Spec.Argon2.Params} {s t : State} {memory : Array VG.Spec.Argon2.Block} {acc : VG.Spec.Argon2.Block}
    (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s) (done : ReduceLane.Done s t p memory acc) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) d) 64 = s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
          omega))) (by decide)

end VG.Proof.Argon2.X86_64.ReductionState

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FinalOutputReady`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FinalOutputArgs`. -/
section
/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def changed : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8]

structure Arguments (s t : State) : Prop where
  input : t.gpr .rdi = ReductionState.matrix s
  inputLength : t.gpr .rsi = 1024
  output : t.gpr .rdx = VG.Proof.Argon2.X86_64.FinalOutput.output s
  outputLength : t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 264) 64
  work : t.gpr .r8 = VG.Proof.Argon2.X86_64.FinalOutput.work s
  keeps : Divide.Keeps VG.Proof.Argon2.X86_64.FinalOutput.changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block Impl.Argon2.X86_64.FinalOutput.args) s (VG.Proof.Argon2.X86_64.FinalOutput.Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FinalOutput.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, VG.Proof.Argon2.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [VG.Proof.Argon2.X86_64.FinalOutput.changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem Arguments.regs {s t : State} (h : VG.Proof.Argon2.X86_64.FinalOutput.Arguments s t) (r : Reg) (hr : r ∈ calleeSaved) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ VG.Proof.Argon2.X86_64.FinalOutput.changed := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.X86_64.FinalOutput
end

/-! Final output uses matrix block zero and the original disjoint hash scratch allocation. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  positive : 1 ≤ p.tagLen
  bound : p.tagLen < 2 ^ 32
  reads : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  tagWord : s.mem.readW (off (s.gpr .rbp) 264) 64 = BitVec.ofNat 64 p.tagLen
  input : Covers [⟨ReductionState.matrix s, 1024⟩] (s.rd ++ s.wr)
  outputWrite : Covers [⟨VG.Proof.Argon2.X86_64.FinalOutput.output s, p.tagLen⟩] s.wr
  workWrite : (⟨VG.Proof.Argon2.X86_64.FinalOutput.work s, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨ReductionState.matrix s, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FinalOutput.work s, 16384⟩
  outputWork : (⟨VG.Proof.Argon2.X86_64.FinalOutput.output s, p.tagLen⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FinalOutput.work s, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨ReductionState.matrix s, 1024⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨VG.Proof.Argon2.X86_64.FinalOutput.output s, p.tagLen⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨VG.Proof.Argon2.X86_64.FinalOutput.work s, 16384⟩

theorem Arguments.ready {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.FinalOutput.Ready p s) (a : VG.Proof.Argon2.X86_64.FinalOutput.Arguments s t) :
    FinalCall.CallReady p.tagLen t := by
  have sp := a.regs .rsp (by simp [calleeSaved])
  constructor
  · exact h.positive
  · exact h.bound
  · rw [a.input, a.keeps.rd, a.keeps.wr]; exact h.input
  · rw [a.output, a.keeps.wr]; exact h.outputWrite
  · rw [a.work, a.keeps.wr]; exact h.workWrite
  · rw [a.input, a.work]; exact h.inputWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [a.input, sp]; exact h.stackInput
  · rw [a.output, sp]; exact h.stackOutput
  · rw [a.work, sp]; exact h.stackWork

end VG.Proof.Argon2.X86_64.FinalOutput

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FinishReady`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ReduceLanesBody`. -/
section
/-! One reduction iteration advances a public lane and preserves the accumulator invariant. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (lane : Nat) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  active : lane < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Done (s t : State) (p : Params) (lane : Nat) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 (lane + 1)
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  cf : t.cf = decide (lane + 1 < p.lanes)
  next : lane + 1 < p.lanes → VG.Proof.Argon2.X86_64.ReduceLanes.Ready p (lane + 1) t

theorem body_ok (s : State) (p : Params) (lane : Nat) (h : VG.Proof.Argon2.X86_64.ReduceLanes.Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.body s
      (VG.Proof.Argon2.X86_64.ReduceLanes.Done s · p lane memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  unfold Impl.Argon2.X86_64.ReduceLanes.body Impl.Argon2.X86_64.ReduceLanes.advance
  refine WP.seq ((ReduceLane.code_ok s p lane h.allocation h.active h.laneWord memory acc represented).mono ?_)
  intro a reduced
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 184) 8 := by
    rw [reduced.rd, reduced.wr, reduced.regs .rbp (by simp [calleeSaved])]; exact h.lanesRead
  have word := (ReductionState.frame_word h.allocation reduced 184 (by decide)).trans h.lanesWord
  refine (FillLanes.advance_ok a read).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : matrix t = matrix a := by unfold matrix; rw [keeps.mem, bp]
  have added : a.gpr .rbx + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [reduced.regs .rbx (by simp [calleeSaved]), h.laneWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  refine ⟨reduced.represented.of_state bp keeps.mem, base.trans reduced.base, nextWord,
    ?_, keeps.rd.trans reduced.rd, keeps.wr.trans reduced.wr, ?_, keeps.mxcsr.trans reduced.mxcsr, ?_, ?_⟩
  · intro r hr bx
    exact (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using bx)).trans (reduced.regs r hr)
  · rw [keeps.mem]; exact reduced.frame
  · rw [flag, added, word, ReferenceMap.word_nat (lane + 1) (by have bound := h.lanesBound; have active := h.active; omega),
      ReferenceMap.word_nat p.lanes (Nat.lt_trans h.lanesBound (by decide))]
  · intro active
    refine ⟨reduced.ready.of_state bp (keeps.regs .r12 (by decide)) keeps.mem keeps.rd keeps.wr,
      active, h.lanesBound, nextWord, ?_, ?_⟩
    · rw [keeps.rd, keeps.wr, bp]; exact read
    · rw [keeps.mem, bp]; exact word

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Merged from `Proof.Argon2.X86_64.ReductionInit`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReductionClear`. -/
section
/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.X86_64.ReductionState

open VG VG.X86_64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : VG.Proof.Argon2.X86_64.ReductionState.Ready p t
  represented : Represents p memory zeroBlock t
  base : matrix t = matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clear_ok (s : State) (p : Params) (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s)
    (dest : s.gpr .rdi = matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.ClearBlock.code s (VG.Proof.Argon2.X86_64.ReductionState.Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ClearBlock.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .rbp (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  have base : matrix t = matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .r12 (by decide)).trans h.length⟩
    · rw [keeps.2.1, keeps.2.2, bp]; exact h.read
    · rw [base, keeps.2.2]; exact h.write
    · rw [base, bp]; exact h.frame
  · constructor
    · rw [base]; exact zero
    · intro lane active
      rw [base]
      apply Eq.trans _ (represented.block _ (Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active).2)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (matrix s) p.blocks (Proof.Argon2.lastIndex p lane) 0 h.bound
          bounds.2 (by omega) (by omega)

theorem Cleared.frame_word {p : Params} {s t : State} {memory : Array Block}
    (ready : VG.Proof.Argon2.X86_64.ReductionState.Ready p s) (done : VG.Proof.Argon2.X86_64.ReductionState.Cleared s t p memory) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.keeps.1 .rbp (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega))) (by decide)

end VG.Proof.Argon2.X86_64.ReductionState
end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanes`. -/
section
/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : VG.Proof.Argon2.X86_64.ReduceLanes.Done s t p lane memory acc) (last : lane + 1 = p.lanes) : VG.Proof.Argon2.X86_64.ReduceLanes.Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : VG.Proof.Argon2.X86_64.ReduceLanes.Done s a p lane memory acc) (rest : VG.Proof.Argon2.X86_64.ReduceLanes.Finished a t p memory result) : VG.Proof.Argon2.X86_64.ReduceLanes.Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : VG.Proof.Argon2.X86_64.ReduceLanes.Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.loop s
      (VG.Proof.Argon2.X86_64.ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory lane count acc)) := by
  induction count generalizing s lane acc with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.X86_64.ReduceLanes.body_ok s p lane h memory acc represented
    rw [Proof.Argon2.reduction_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Establish the invariant for reducing all lanes, retaining the input matrix's last blocks. -/

namespace VG.Proof.Argon2.X86_64.ReductionInit

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  lanesBound : p.lanes < 2 ^ 32
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8) :
    WP isa (.block Impl.Argon2.X86_64.ReductionInit.setup) s fun t =>
      t.gpr .rdi = matrix s ∧ t.gpr .rbx = 0 ∧ Divide.Keeps [.rdi, .rbx] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReductionInit.setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, VG.Proof.Argon2.X86_64.ea_at, read, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg, reduceCtorEq, ite_false]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

structure Prepared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : ReduceLanes.Ready p 0 t
  represented : ReductionState.Represents p memory zeroBlock t
  base : matrix t = matrix s
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem code_ok (s : State) (p : Params) (h : VG.Proof.Argon2.X86_64.ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.ReductionInit.code s (VG.Proof.Argon2.X86_64.ReductionInit.Prepared s · p memory) := by
  unfold Impl.Argon2.X86_64.ReductionInit.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReductionInit.setup_ok s h.allocation.read).mono ?_)
  rintro a ⟨dest, lane, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : matrix a = matrix s := by unfold matrix; rw [keeps.mem, bp]
  have ha := h.allocation.of_state bp (keeps.regs .r12 (by decide)) keeps.mem keeps.rd keeps.wr
  have rep : Proof.Argon2.Represents a.mem (matrix a) p.blocks memory := by rw [keeps.mem, base]; exact represented
  refine (ReductionState.clear_ok a p ha (dest.trans base.symm) memory rep).mono ?_
  intro t cleared
  refine ⟨⟨cleared.ready, ha.positive, h.lanesBound,
    (cleared.keeps.1 .rbx (by decide)).trans lane, ?_, ?_⟩,
    cleared.represented, cleared.base.trans base, ?_, cleared.keeps.2.1.trans keeps.rd,
    cleared.keeps.2.2.trans keeps.wr, ?_, cleared.mxcsr.trans keeps.mxcsr⟩
  · rw [cleared.keeps.2.1, cleared.keeps.2.2, cleared.keeps.1 .rbp (by decide), keeps.rd, keeps.wr, bp]
    exact h.lanesRead
  · rw [cleared.frame_word ha 184 (by decide), keeps.mem, bp]; exact h.lanesWord
  · intro r hr bx
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notDest : r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (cleared.keeps.1 r ne).trans (keeps.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨notDest, bx⟩))
  · have frame := cleared.frame
    rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.X86_64.ReductionInit
end

/-! Merged from `Proof.Argon2.X86_64.ReductionInitCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReducePointersCT`. -/
section
/-! Pointer preparation reads one public frame location and performs fixed arithmetic. -/

namespace VG.Proof.Argon2.X86_64.ReducePointers

open VG VG.X86_64

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.ReducePointers.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReducePointers
end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanesCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceLanesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceLaneCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceBlockCT`. -/
section
/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceBlock

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) VG.Impl.Argon2.X86_64.ReduceBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReduceBlock
end

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceLane

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.ReductionState.Ready p s
  right : VG.Proof.Argon2.X86_64.ReductionState.Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .rbx = BitVec.ofNat 64 lane
  rightLane : t.gpr .rbx = BitVec.ofNat 64 lane
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReduceLane.Related p lane) Impl.Argon2.X86_64.ReducePointers.code
      (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := VG.Proof.Argon2.X86_64.ReduceLane.Related p lane) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .rbp) 232) 64 = t.mem.readW (off (t.gpr .rbp) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReduceLane.Related p lane) Impl.Argon2.X86_64.ReduceLane.code (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.ReduceLane.pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.X86_64.ReduceLane
end

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.ReduceLanes.Ready p lane s
  right : VG.Proof.Argon2.X86_64.ReduceLanes.Ready p lane t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReduceLanes.advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReduceLanes.Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → VG.Proof.Argon2.X86_64.ReduceLanes.Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.matrices⟩
  cases ea with
  | seq reduceA advanceA =>
    cases eb with
    | seq reduceB advanceB =>
      obtain ⟨reduceTrace, _⟩ := ReduceLane.code_rel p lane _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, reducedA⟩ := ReduceLane.code_ok s p lane hp.left.allocation hp.left.active
        hp.left.laneWord leftMemory leftAcc hp.leftRep
      obtain ⟨_, sb, runB, reducedB⟩ := ReduceLane.code_ok t p lane hp.right.allocation hp.right.active
        hp.right.laneWord rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have bases := (reducedA.regs .rbp (by simp [calleeSaved])).trans
        (hp.bases.trans (reducedB.regs .rbp (by simp [calleeSaved])).symm)
      obtain ⟨advanceTrace, _⟩ := VG.Proof.Argon2.X86_64.ReduceLanes.advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.X86_64.ReduceLanes.body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.X86_64.ReduceLanes.body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReduceLanes.Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    VG.Proof.Argon2.X86_64.ReduceLanes.Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.ReduceLanes.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.X86_64.ReduceLanes.body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.X86_64.ReduceLanes.body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega, j + 1, _, _, by omega, by omega, next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.X86_64.ReductionInit

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.ReductionInit.Ready p s
  right : VG.Proof.Argon2.X86_64.ReductionInit.Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReductionInit.setup) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem clear_rel : RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi)
    Impl.Argon2.X86_64.ClearBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.X86_64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, _⟩ := VG.Proof.Argon2.X86_64.ReductionInit.setup_rel _ _ _ _ _ _ hp.bases setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := VG.Proof.Argon2.X86_64.ReductionInit.setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := VG.Proof.Argon2.X86_64.ReductionInit.setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := VG.Proof.Argon2.X86_64.ReductionInit.clear_rel _ _ _ _ _ _ (destA.trans (hp.matrices.trans destB.symm)) clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.X86_64.ReductionInit.code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.X86_64.ReductionInit.code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReductionInit
end

/-! Merged from `Proof.Argon2.X86_64.FinalReduction`. -/
section
/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.X86_64.FinalReduction

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.X86_64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.mxcsr.trans prepared.mxcsr, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.X86_64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.X86_64.FinalReduction
end

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : VG.Proof.Argon2.X86_64.Finish.Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := VG.Proof.Argon2.X86_64.Finish.frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := VG.Proof.Argon2.X86_64.Finish.frame_word ready.reduction done 248 (by decide)
  refine ⟨ready.output.positive, ready.output.bound, ?_,
    (VG.Proof.Argon2.X86_64.Finish.frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.X86_64.Finish

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillFinish`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FinishStage`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FinalOutput`. -/
section
/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (VG.Proof.Argon2.X86_64.FinalOutput.output s) p.tagLen = VG.Spec.Argon2.finish p memory
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.X86_64.FinalOutput.output s, p.tagLen⟩, ⟨VG.Proof.Argon2.X86_64.FinalOutput.work s, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : VG.Proof.Argon2.X86_64.FinalOutput.Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.X86_64.FinalOutput.code name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.FinalOutput.Done s · p memory) := by
  unfold Impl.Argon2.X86_64.FinalOutput.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FinalOutput.args_ok s h.reads).mono ?_)
  intro a args
  have length := args.outputLength.trans h.tagWord
  refine (FinalCall.hPrime_call_ok v name p.tagLen a (args.ready h) args.inputLength length).mono ?_
  intro t called
  refine ⟨?_, fun r hr => (called.regs r hr).trans (args.regs r hr), called.rd.trans args.keeps.rd,
    called.wr.trans args.keeps.wr, ?_⟩
  · have input : bytesAt a.mem (a.gpr .rdi) 1024 =
        serialize (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) := by
      rw [args.keeps.mem, args.input, ← Proof.Argon2.serialize_blockAt, block]
    rw [Proof.Argon2.finish_reduction]
    have digest := called.digest
    rw [args.output, input] at digest
    exact digest
  · have frame := called.frame
    rw [args.output, args.work, args.regs .rsp (by simp [calleeSaved]), args.keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.X86_64.FinalOutput
end

/-! The complete reviewed finish computation, with its enclosing frame and ABI obligations. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

def writes (s : State) (p : Params) : List Region :=
  [⟨matrix s, 1024⟩, ⟨FinalOutput.output s, p.tagLen⟩,
    ⟨FinalOutput.work s, 16384⟩, below (s.gpr .rsp) 24]

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = Spec.Argon2.finish p memory
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.Finish.writes s p) s.mem t.mem

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : VG.Proof.Argon2.X86_64.Finish.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa (Impl.Argon2.X86_64.Finish.code name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.Finish.Done s · p memory) := by
  unfold Impl.Argon2.X86_64.Finish.code
  refine WP.seq ((FinalReduction.code_ok s p h.reduction memory represented).mono ?_)
  intro a reduced
  refine (FinalOutput.code_ok v name a p (VG.Proof.Argon2.X86_64.Finish.output_ready h reduced) memory reduced.represented.accumulator).mono ?_
  intro t written
  have output : FinalOutput.output a = FinalOutput.output s := VG.Proof.Argon2.X86_64.Finish.frame_word h.reduction reduced 256 (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := VG.Proof.Argon2.X86_64.Finish.frame_word h.reduction reduced 248 (by decide)
  refine ⟨?_, fun r hr bx => (written.regs r hr).trans (reduced.regs r hr bx),
    written.rd.trans reduced.rd, written.wr.trans reduced.wr, ?_⟩
  · have digest := written.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (VG.Proof.Argon2.X86_64.Finish.writes s p) s.mem a.mem := reduced.frame.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, by simp [VG.Proof.Argon2.X86_64.Finish.writes], fun _ h => h⟩)
    have lastFrame := written.frame
    rw [output, work, reduced.regs .rsp (by simp [calleeSaved]) (by decide)] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [VG.Proof.Argon2.X86_64.Finish.writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.Finish
end

/-! Merged from `Proof.Argon2.X86_64.FillFinishReady`. -/
section
/-! The complete filling loop retains the original final-call allocations and public metadata. -/

namespace VG.Proof.Argon2.X86_64.FillFinish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

theorem finish_ready {s t : State} {p : Params} {state : FillState}
    (filling : FillIterations.Ready p 0 s) (ready : Finish.Ready p s)
    (done : FillIterations.Finished s t p state) : Finish.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)
  have base : matrix t = matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word filling 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word filling 248 (by decide) (by decide)
  constructor
  · have a := ready.reduction.allocation
    refine ⟨⟨a.positive, a.minimum, a.bound, ?_, ?_, ?_, ?_⟩, ready.reduction.lanesBound, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact a.read
    · rw [base, done.wr]; exact a.write
    · rw [base, bp]; exact a.frame
    · exact (done.regs .r12 (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans a.length
    · rw [done.rd, done.wr, bp]; exact ready.reduction.lanesRead
    · exact (done.frame_word filling 184 (by decide) (by decide)).trans ready.reduction.lanesWord
  · refine ⟨ready.output.positive, ready.output.bound, ?_,
      (done.frame_word filling 264 (by decide) (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact ready.output.reads
    · rw [base, done.rd, done.wr]; exact ready.output.input
    · rw [output, done.wr]; exact ready.output.outputWrite
    · rw [work, done.wr]; exact ready.output.workWrite
    · rw [base, work]; exact ready.output.inputWork
    · rw [output, work]; exact ready.output.outputWork
    · rw [sp, base]; exact ready.output.stackInput
    · rw [sp, output]; exact ready.output.stackOutput
    · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.X86_64.FillFinish
end

/-! The complete filling and finalization stages produce the reviewed final tag. -/

namespace VG.Proof.Argon2.X86_64.FillFinish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  filling : FillIterations.Ready p 0 s
  finish : Finish.Ready p s
  positive : 0 < p.passes

def writes (s : State) (p : Params) : List Region := FillIterations.writes s p ++ Finish.writes s p

structure Done (s t : State) (p : Params) (state : FillState) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen =
    Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes state).memory
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillFinish.writes s p) s.mem t.mem

theorem code_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : VG.Proof.Argon2.X86_64.FillFinish.Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.X86_64.FillFinish.code name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.FillFinish.Done s · p state) := by
  unfold Impl.Argon2.X86_64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (VG.Proof.Argon2.X86_64.FillFinish.finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : matrix a = matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (VG.Proof.Argon2.X86_64.FillFinish.writes s p) s.mem a.mem := filled.frame.sub (by
      intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    have lastFrame := finished.frame
    rw [Finish.writes, base, output, work,
      filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

end VG.Proof.Argon2.X86_64.FillFinish

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit`. -/
section

/-! # Checked literals for the public dimension setup blocks -/

namespace VG

materialize_code Impl.Argon2.X86_64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.X86_64.MemoryInit.lanesSetupCode

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialLayout`. -/
section

/-! # The stack inputs and scratch allocation used by H₀ -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def slots : List Nat := [72, 80, 88, 96, 104, 112, 176, 184, 200, 208, 216, 224, 264]

def wordAt (s : State) (d : Nat) : Addr :=
  s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64

def inputRegion (s : State) (pointerOffset lengthOffset : Nat) : Region :=
  ⟨VG.Proof.Argon2.X86_64.Initial.wordAt s pointerOffset, (VG.Proof.Argon2.X86_64.Initial.wordAt s lengthOffset).toNat⟩

/-- Hash calls and argument preparation preserve these registers and bytes.
`r12` and `r14` are the running count and the current input length. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16] s.mem t.mem

theorem Keeps.rbx {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Keeps s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.rbp {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Keeps s t) : t.gpr .rbp = s.gpr .rbp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.rsp {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Keeps s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.trans {s t u : State} (h : VG.Proof.Argon2.X86_64.Initial.Keeps s t) (k : VG.Proof.Argon2.X86_64.Initial.Keeps t u) : VG.Proof.Argon2.X86_64.Initial.Keeps s u :=
  ⟨fun r hr h1 h2 => (k.regs r hr h1 h2).trans (h.regs r hr h1 h2),
    k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.rbx, h.rsp] using k.frame)⟩

theorem Keeps.of_hash {s t : State} (h : HPrime.Keeps s t) : VG.Proof.Argon2.X86_64.Initial.Keeps s t :=
  ⟨fun r hr _ _ => h.regs r hr, h.rd, h.wr, h.frame⟩

structure Space (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 16)
  readable : ∀ d ∈ VG.Proof.Argon2.X86_64.Initial.slots, InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8
  output : InRegions s.wr (s.gpr .rbp) 64

theorem Space.keeps {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Space s) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t) : VG.Proof.Argon2.X86_64.Initial.Space t := by
  constructor
  · rw [k.rbx, k.wr]; exact h.work
  · rw [k.rbx, k.rsp]; exact h.stackWork
  · rw [k.rbp, k.rbx]; exact h.frameWork
  · rw [k.rbp, k.rsp]; exact h.frameStack
  · intro d hd; rw [k.rbp, k.rd, k.wr]; exact h.readable d hd
  · rw [k.rbp, k.wr]; exact h.output

theorem Space.word_keeps {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Space s) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t)
    (d : Nat) (hd : d + 8 ≤ 272) : VG.Proof.Argon2.X86_64.Initial.wordAt t d = VG.Proof.Argon2.X86_64.Initial.wordAt s d := by
  unfold VG.Proof.Argon2.X86_64.Initial.wordAt
  rw [k.rbp]
  apply k.frame.readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ hd (by omega)) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
  · exact h.frameStack

theorem Space.write {s : State} (h : VG.Proof.Argon2.X86_64.Initial.Space s) (d n : Nat) (hd : d + n ≤ 16384) :
    InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) n :=
  ⟨_, h.work, Offset.contains_base _ hd (by omega)⟩

theorem Space.input_keeps {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Space s) (k : VG.Proof.Argon2.X86_64.Initial.Keeps s t)
    (po lo : Nat) (hp : po + 8 ≤ 272) (hl : lo + 8 ≤ 272) :
    VG.Proof.Argon2.X86_64.Initial.inputRegion t po lo = VG.Proof.Argon2.X86_64.Initial.inputRegion s po lo := by
  simp only [VG.Proof.Argon2.X86_64.Initial.inputRegion, h.word_keeps k po hp, h.word_keeps k lo hl]

theorem Keeps.bytes {s t : State} (h : VG.Proof.Argon2.X86_64.Initial.Keeps s t) (r : Region)
    (work : r.Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stack : r.Disjoint (below (s.gpr .rsp) 16)) (bound : r.len ≤ 2 ^ 64) :
    bytesAt t.mem r.base r.len = bytesAt s.mem r.base r.len := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := r) _ bound hi
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact work.sub_right (Region.sub_prefix (by decide))
  · exact stack

end VG.Proof.Argon2.X86_64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitFill`. -/
section

/-! Merged from `Proof.Argon2.X86_64.MemoryInitBlock`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitArgs`. -/
section
/-! # The 72-byte H₀, column and lane input to memory initialization -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

def blockMem (m : Mem) (p : Addr) (column : Nat) (lane : Addr) : Mem :=
  (m.writeW (p + 64) (BitVec.ofNat 32 column)).writeW (p + 68) (lane.setWidth 32)

theorem blockMem_frame (m : Mem) (p : Addr) (column : Nat) (lane : Addr) :
    Frame [⟨p + 64, 8⟩] m (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane) := by
  unfold VG.Proof.Argon2.X86_64.MemoryInit.blockMem
  have first : Frame [⟨p + 64, 8⟩] m (m.writeW (p + 64) (BitVec.ofNat 32 column)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa only [BitVec.add_zero] using
        Offset.contains_base (p + 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide))
  apply first.writeW (List.mem_singleton_self _)
  have eq : p + 68 = (p + 64) + BitVec.ofNat 64 4 := by rw [BitVec.add_assoc]; rfl
  rw [eq]
  exact Offset.contains_base _ (by decide : 4 + 4 ≤ 8) (by decide)

theorem blockMem_bytes (m : Mem) (p : Addr) (column : Nat) (lane : Addr) :
    bytesAt (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane) p 72 =
      bytesAt m p 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 lane.toNat := by
  have first : bytesAt (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane) p 64 = bytesAt m p 64 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply (VG.Proof.Argon2.X86_64.MemoryInit.blockMem_frame m p column lane).bytes (R := ⟨p, 64⟩) _
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
    · intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.base_disjoint _ (by decide) (by decide)

  have columnWord : (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane).readW (p + 64) 32 = BitVec.ofNat 32 column := by
    unfold VG.Proof.Argon2.X86_64.MemoryInit.blockMem
    rw [Mem.readW_writeW_sep ?_ (by decide), Mem.readW_writeW_self32]
    exact Offset.sep p (by decide) (by decide) (by decide)
  have laneWord : (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane).readW (p + 68) 32 = lane.setWidth 32 :=
    Mem.readW_writeW_self32 _ _ _
  have words := Proof.Blake2.bytesAt_add (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane) (p + 64) 4 4
  have pos : p + 64 + BitVec.ofNat 64 4 = p + 68 := by rw [BitVec.add_assoc]; rfl
  rw [pos, ← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl),
    ← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl), columnWord, laneWord] at words
  have header := Proof.Blake2.bytesAt_add (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane) p 64 8
  change bytesAt (VG.Proof.Argon2.X86_64.MemoryInit.blockMem m p column lane) (p + 64) 8 = _ at words
  rw [show BitVec.ofNat 64 64 = (64 : Addr) from rfl, first, words, ← BitVec.ofNat_toNat 32 lane, ← List.append_assoc] at header
  exact header

structure BlockArgs (s t : State) (column : Nat) : Prop where
  input : t.gpr .rdi = s.gpr .rbp
  inputLength : t.gpr .rsi = 72
  output : t.gpr .rdx = s.gpr .r14
  outputLength : t.gpr .rcx = 1024
  work : t.gpr .r8 = s.gpr .rbx
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 →
    t.gpr r = s.gpr r
  mem : t.mem = VG.Proof.Argon2.X86_64.MemoryInit.blockMem s.mem (s.gpr .rbp) column (s.gpr .r12)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem blockArgs_ok (s : State) (column : Nat)
    (colWrite : InRegions s.wr (s.gpr .rbp + 64) 4)
    (laneWrite : InRegions s.wr (s.gpr .rbp + 68) 4) :
    WP isa (.block (blockArgs column)) s (fun t => VG.Proof.Argon2.X86_64.MemoryInit.BlockArgs s t column) := by
  apply WP.of_runBlock
  simp only [blockArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.setReg32, State.store32, HPrime.ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 64 = (64 : Addr) from rfl,
    show BitVec.ofNat 64 68 = (68 : Addr) from rfl,
    reduceCtorEq, ite_true, ite_false, colWrite, laneWrite,
    Option.map_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, h5, h6, ite_false]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Initializing a block while preserving H₀ and the public lane counters -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure BlockReady (s : State) : Prop where
  input : Covers [⟨s.gpr .rbp, 72⟩] s.wr
  output : Covers [⟨s.gpr .r14, 1024⟩] s.wr
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  frameWork : (⟨s.gpr .rbp, 72⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  frameOutput : (⟨s.gpr .rbp, 72⟩ : Region).Disjoint ⟨s.gpr .r14, 1024⟩
  outputWork : (⟨s.gpr .r14, 1024⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackFrame : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbp, 72⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r14, 1024⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbx, 16384⟩

theorem BlockArgs.regs {s t : State} {column : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockArgs s t column)
    (r : Reg) (hr : r ∈ calleeSaved) : t.gpr r = s.gpr r := by
  have hn : r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem BlockReady.prefix {s : State} (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s) (d : Nat)
    (bound : d + 4 ≤ 72) : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 4 := by
  exact h.input _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem BlockArgs.ready {s t : State} {column : Nat} (a : VG.Proof.Argon2.X86_64.MemoryInit.BlockArgs s t column)
    (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s) : VG.Proof.Argon2.X86_64.MemoryInit.CallReady t := by
  have base := a.regs .rbx (by decide)
  have sp := a.regs .rsp (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a.input, a.rd, a.wr]
    intro p n ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst r
    obtain ⟨r, hr, hc'⟩ := h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [a.output, a.wr]; exact h.output
  · rw [a.work, a.wr]; exact h.work
  · rw [a.input, a.work]; exact h.frameWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [sp, a.input]; exact h.stackFrame
  · rw [sp, a.output]; exact h.stackOutput
  · rw [sp, a.work]; exact h.stackWork

structure BlockDone (s t : State) (column : Nat) : Prop where
  digest : bytesAt t.mem (s.gpr .r14) 1024 = Spec.Argon2.hPrime 1024
    (bytesAt s.mem (s.gpr .rbp) 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 (s.gpr .r12).toNat)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .r14, 1024⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem block_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (column : Nat) (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s) :
    WP isa (VG.Impl.Argon2.X86_64.MemoryInit.block name (HPrime.hash v) column) s (fun t => VG.Proof.Argon2.X86_64.MemoryInit.BlockDone s t column) := by
  unfold VG.Impl.Argon2.X86_64.MemoryInit.block
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.blockArgs_ok s column
    (by simpa only [show BitVec.ofNat 64 64 = (64 : Addr) from rfl] using h.prefix 64 (by decide))
    (by simpa only [show BitVec.ofNat 64 68 = (68 : Addr) from rfl] using h.prefix 68 (by decide))).mono ?_)
  intro a ha
  refine (VG.Proof.Argon2.X86_64.MemoryInit.hPrime_call_ok v name a (ha.ready h) ha.inputLength ha.outputLength).mono ?_
  intro t ht
  refine ⟨?_, fun r hr => (ht.regs r hr).trans (ha.regs r hr),
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
  · have digest := ht.digest
    rw [ha.output, ha.input, ha.mem, VG.Proof.Argon2.X86_64.MemoryInit.blockMem_bytes] at digest
    exact digest
  · have argsFrame : Frame [⟨s.gpr .r14, 1024⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem a.mem := by
      rw [ha.mem]
      exact (VG.Proof.Argon2.X86_64.MemoryInit.blockMem_frame _ _ _ _).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    apply argsFrame.trans
    have frame := ht.frame
    rw [ha.output, ha.work, ha.regs .rsp (by decide)] at frame
    exact frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitSpace`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitMatrix`. -/
section
/-! # Matrix cells and the memory preserved by initialization calls -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

theorem clearMem_block (m : Mem) (p : Addr) (blocks k : Nat)
    (bound : 1024 * blocks < 2 ^ 64) (hk : k < blocks) :
    blockAt (clearMem m p (128 * blocks)) (p + BitVec.ofNat 64 (1024 * k)) = zeroBlock := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, zeroBlock, Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 1024 * k + 8 * j = 8 * (128 * k + j) by omega]
  exact clearMem_word m p (128 * blocks) (128 * k + j) (by omega) (by omega)

theorem blockAt_frame {m m' : Mem} {rs : List Region} (frame : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  rw [← Proof.Argon2.parseBlock_bytesAt, ← Proof.Argon2.parseBlock_bytesAt]
  apply congrArg parseBlock
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  exact frame.bytes (R := ⟨p, 1024⟩) sep (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi

theorem BlockDone.h0 {s t : State} {column : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockDone s t column)
    (ready : VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s) : bytesAt t.mem (s.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .rbp, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ready.frameOutput.sub_left (Region.sub_prefix (by decide))
  · exact ready.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact ready.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem BlockDone.block {s t : State} {column : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockDone s t column) :
    blockAt t.mem (s.gpr .r14) = parseBlock
      (Proof.Argon2.initialBytes (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat column) :=
  Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ h.digest

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Permissions for the matrix, derivation frame and hash scratch -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Space (s : State) (memory : Addr) (bytes : Nat) : Prop where
  matrix : Covers [⟨memory, bytes⟩] s.wr
  frame : Covers [⟨s.gpr .rbp, 72⟩] s.wr
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  frameMatrix : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨memory, bytes⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  matrixWork : (⟨memory, bytes⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackFrame : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbp, 272⟩
  stackMatrix : (below (s.gpr .rsp) 24).Disjoint ⟨memory, bytes⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbx, 16384⟩
  bound : bytes < 2 ^ 64

theorem Space.same {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory bytes)
    (wr : t.wr = s.wr) (bp : t.gpr .rbp = s.gpr .rbp)
    (bx : t.gpr .rbx = s.gpr .rbx) (sp : t.gpr .rsp = s.gpr .rsp) : VG.Proof.Argon2.X86_64.MemoryInit.Space t memory bytes := by
  constructor
  · rw [wr]; exact h.matrix
  · rw [bp, wr]; exact h.frame
  · rw [bx, wr]; exact h.work
  · rw [bp]; exact h.frameMatrix
  · rw [bp, bx]; exact h.frameWork
  · rw [bx]; exact h.matrixWork
  · rw [sp, bp]; exact h.stackFrame
  · rw [sp]; exact h.stackMatrix
  · rw [sp, bx]; exact h.stackWork
  · exact h.bound

theorem Space.blockReady {s : State} {memory : Addr} {bytes d : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory bytes) (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d)
    (bound : d + 1024 ≤ bytes) : VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s := by
  have outputSub : Region.Sub ⟨s.gpr .r14, 1024⟩ ⟨memory, bytes⟩ := by
    rw [dst]; exact Offset.sub_base _ bound
  have outputCover : Covers [⟨s.gpr .r14, 1024⟩] s.wr := by
    have narrow : Covers [⟨s.gpr .r14, 1024⟩] [⟨memory, bytes⟩] := Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, d, dst, bound⟩)
    exact fun p n hp => h.matrix p n (narrow p n hp)
  exact ⟨h.frame, outputCover, h.work,
    h.frameWork.sub_left (Region.sub_prefix (by decide)),
    (h.frameMatrix.sub_left (Region.sub_prefix (by decide))).sub_right outputSub,
    h.matrixWork.sub_left outputSub,
    h.stackFrame.sub_right (Region.sub_prefix (by decide)),
    h.stackMatrix.sub_right outputSub, h.stackWork⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitLane`. -/
section
/-! # Initializing both leading blocks of one lane -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LaneDone (s t : State) : Prop where
  first : bytesAt t.mem (s.gpr .r14) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat 0
  second : bytesAt t.mem (s.gpr .r14 + 1024) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat 1
  destination : t.gpr .r14 = s.gpr .r14 + s.gpr .r13
  lane : t.gpr .r12 = s.gpr .r12 + 1
  remaining : t.gpr .r15 = s.gpr .r15 - 1
  zf : t.zf = some (s.gpr .r15 - 1 == 0)
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .r14, 2048⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem frame_widen {m m' : Mem} {p : Addr} {d : Nat} {work stack headRegion : Region}
    (h : Frame [⟨p + BitVec.ofNat 64 d, 1024⟩, work, stack, headRegion] m m')
    (bound : d + 1024 ≤ 2048) : Frame [⟨p, 2048⟩, work, stack, headRegion] m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ bound⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))), fun _ h => h⟩

theorem lane_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (memory : Addr) (bytes d : Nat) (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory bytes)
    (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d) (bound : d + 2048 ≤ bytes) :
    WP isa (lane name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.MemoryInit.LaneDone s) := by
  have ready := space.blockReady dst (by omega)
  unfold lane
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.block_ok v name s 0 ready).mono ?_)
  intro a ha
  have spaceA := space.same ha.wr (ha.regs .rbp (by decide))
    (ha.regs .rbx (by decide)) (ha.regs .rsp (by decide))
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.advance_ok a).mono ?_)
  intro b hb
  have spaceB := spaceA.same hb.wr (hb.other .rbp (by decide))
    (hb.other .rbx (by decide)) (hb.other .rsp (by decide))
  have base : b.gpr .r14 = s.gpr .r14 + 1024 := by rw [hb.destination, ha.regs .r14 (by decide)]
  have bp : b.gpr .rbp = s.gpr .rbp := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have bx : b.gpr .rbx = s.gpr .rbx := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have sp : b.gpr .rsp = s.gpr .rsp := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have laneB : b.gpr .r12 = s.gpr .r12 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have strideB : b.gpr .r13 = s.gpr .r13 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have remainingB : b.gpr .r15 = s.gpr .r15 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have dstB : b.gpr .r14 = memory + BitVec.ofNat 64 (d + 1024) := by
    rw [base, dst, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have readyB := spaceB.blockReady dstB (by omega)
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.block_ok v name b 1 readyB).mono ?_)
  intro c hc
  refine (laneEnd_ok c).mono ?_
  intro t ht
  have secondFrame := hc.frame
  rw [base, bx, sp, bp] at secondFrame
  have keptFirst : bytesAt c.mem (s.gpr .r14) 1024 = bytesAt b.mem (s.gpr .r14) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply secondFrame.bytes (R := ⟨s.gpr .r14, 1024⟩) _
      (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · rw [dst]; exact space.matrixWork.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.stackMatrix.symm.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.frameMatrix.symm.sub_left (Offset.sub_base _ (by omega)) |>.sub_right
        (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
  have h0B : bytesAt b.mem (b.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
    rw [hb.mem, bp]; exact ha.h0 ready
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),
    ht.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)), ?_⟩
  · rw [ht.mem, keptFirst, hb.mem]; exact ha.digest
  · have digest := hc.digest
    rw [base, h0B, laneB] at digest
    rw [ht.mem]; exact digest
  · rw [ht.destination, hc.regs .r14 (by decide), hc.regs .r13 (by decide), base, strideB]
    rw [BitVec.add_assoc, BitVec.add_comm (1024 : Addr), ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  · rw [ht.lane, hc.regs .r12 (by decide), laneB]
  · rw [ht.remaining, hc.regs .r15 (by decide), remainingB]
  · rw [ht.zf, hc.regs .r15 (by decide), remainingB]
  · intro r hr h14 h12 h15
    exact (ht.other r h14 h12 h15).trans ((hc.regs r hr).trans
      ((hb.other r h14).trans (ha.regs r hr)))
  · rw [ht.mem]
    rw [hb.mem] at secondFrame
    have firstFrame := VG.Proof.Argon2.X86_64.MemoryInit.frame_widen (p := s.gpr .r14) (d := 0)
      (by simpa using ha.frame)
      (by decide)
    have finalFrame := VG.Proof.Argon2.X86_64.MemoryInit.frame_widen (p := s.gpr .r14) (d := 1024)
      (by simpa only [show BitVec.ofNat 64 1024 = (1024 : Addr) from rfl] using secondFrame) (by decide)
    exact firstFrame.trans finalFrame

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitStage`. -/
section
/-! # Matrix invariant: completed lanes contain their RFC initialization blocks -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def Initialized (m : Mem) (base : Addr) (lanes q done : Nat) (h0 : List Byte) : Prop :=
  ∀ lane < lanes, ∀ column < q,
    blockAt m (base + BitVec.ofNat 64 (1024 * (lane * q + column))) =
      if lane < done ∧ column < 2 then parseBlock (Proof.Argon2.initialBytes h0 lane column)
      else zeroBlock

theorem cell_bound (lanes q lane column : Nat) (hl : lane < lanes) (hc : column < q) :
    lane * q + column < lanes * q := by
  have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ lanes by omega)
  rw [Nat.add_mul, Nat.one_mul] at mul
  omega

theorem cell_sep (q j lane column : Nat) (hq : 2 ≤ q) (hc : column < q)
    (other : lane ≠ j ∨ 2 ≤ column) :
    1024 * (lane * q + column) + 1024 ≤ 1024 * (j * q) ∨
      1024 * (j * q) + 2048 ≤ 1024 * (lane * q + column) := by
  by_cases lt : lane < j
  · have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  · by_cases gt : j < lane
    · have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lane by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    · have eq : lane = j := by omega
      subst lane
      have large : 2 ≤ column := other.elim (fun h => False.elim (h rfl)) id
      omega

theorem initialized_zero (m : Mem) (base : Addr) (lanes q : Nat)
    (bound : 1024 * (lanes * q) < 2 ^ 64) (h0 : List Byte) :
    VG.Proof.Argon2.X86_64.MemoryInit.Initialized (clearMem m base (128 * (lanes * q))) base lanes q 0 h0 := by
  intro lane hl column hc
  rw [VG.Proof.Argon2.X86_64.MemoryInit.clearMem_block _ _ _ _ bound (VG.Proof.Argon2.X86_64.MemoryInit.cell_bound _ _ _ _ hl hc)]
  simp only [Nat.not_lt_zero, false_and, ite_false]

theorem initialized_lane {s t : State} (memory : Addr) (lanes q j : Nat)
    (h0 : List Byte) (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory (1024 * (lanes * q)))
    (hq : 2 ≤ q) (hj : j < lanes) (lanesBound : lanes < 2 ^ 64)
    (dst : s.gpr .r14 = memory + BitVec.ofNat 64 (1024 * (j * q)))
    (laneReg : s.gpr .r12 = BitVec.ofNat 64 j)
    (hash : bytesAt s.mem (s.gpr .rbp) 64 = h0)
    (initialized : VG.Proof.Argon2.X86_64.MemoryInit.Initialized s.mem memory lanes q j h0) (done : VG.Proof.Argon2.X86_64.MemoryInit.LaneDone s t) :
    VG.Proof.Argon2.X86_64.MemoryInit.Initialized t.mem memory lanes q (j + 1) h0 := by
  have laneValue : (s.gpr .r12).toNat = j := by
    rw [laneReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have currentEnd : 1024 * (j * q) + 2048 ≤ 2 ^ 64 := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    have b := space.bound
    omega
  have cellEnd (lane column : Nat) (hl : lane < lanes) (hc : column < q) :
      1024 * (lane * q + column) + 1024 ≤ 2 ^ 64 := by
    have cell := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q lane column hl hc
    have b := space.bound
    omega
  intro lane hl column hc
  by_cases same : lane = j
  · subst lane
    by_cases first : column = 0
    · subst column
      rw [ite_eq_left (by omega)]
      apply Proof.Argon2.blockAt_of_initialBytes
      have eq := done.first
      rw [hash, laneValue, dst] at eq
      simpa only [Nat.add_zero] using eq
    · by_cases second : column = 1
      · subst column
        rw [ite_eq_left (by omega)]
        apply Proof.Argon2.blockAt_of_initialBytes
        have eq := done.second
        rw [hash, laneValue, dst, BitVec.add_assoc,
          show (1024 : Addr) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add] at eq
        rw [Nat.mul_add, Nat.mul_one]
        exact eq
      · have large : 2 ≤ column := by omega
        have sep := VG.Proof.Argon2.X86_64.MemoryInit.cell_sep q j j column hq hc (Or.inr large)
        have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) =
            blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) := by
          apply VG.Proof.Argon2.X86_64.MemoryInit.blockAt_frame done.frame
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [dst]; exact Offset.disjoint _ sep (cellEnd j column hj hc) currentEnd
          · exact space.matrixWork.sub_left (Offset.sub_base _
              (by have := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q j column hj hc; omega))
          · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
              (by have := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q j column hj hc; omega))
          · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
              (by have := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q j column hj hc; omega)) |>.sub_right
              (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
        rw [kept, initialized j hj column hc]
        simp only [Nat.lt_irrefl, false_and, ite_false, ite_eq_right (by omega : ¬ (j < j + 1 ∧ column < 2))]
  · have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) =
        blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) := by
      apply VG.Proof.Argon2.X86_64.MemoryInit.blockAt_frame done.frame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [dst]
        exact Offset.disjoint _ (VG.Proof.Argon2.X86_64.MemoryInit.cell_sep q j lane column hq hc (Or.inl same))
          (cellEnd lane column hl hc) currentEnd
      · exact space.matrixWork.sub_left (Offset.sub_base _
          (by have := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q lane column hl hc; omega))
      · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
          (by have := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q lane column hl hc; omega))
      · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
          (by have := VG.Proof.Argon2.X86_64.MemoryInit.cell_bound lanes q lane column hl hc; omega)) |>.sub_right
          (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
    rw [kept, initialized lane hl column hc]
    by_cases before : lane < j ∧ column < 2 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitSetup`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitClearSetup`. -/
section
/-! # Clearing the complete allocation using its public block count -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure ClearHeader (s t : State) : Prop where
  destination : t.gpr .r14 = VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset
  count : t.gpr .rax = VG.Proof.Argon2.X86_64.Initial.wordAt s blocksOffset
  zero : t.gpr .rcx = 0
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clearHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8) :
    WP isa (.block clearHeader) s (VG.Proof.Argon2.X86_64.MemoryInit.ClearHeader s) := by
  apply WP.of_runBlock
  simp only [clearHeader, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.setReg32, HPrime.ea_at, memoryOffset, blocksOffset,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 232 = (232 : Addr) from rfl,
    show BitVec.ofNat 64 240 = (240 : Addr) from rfl,
    memoryRead, blocksRead, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

structure ClearSetup (s t : State) : Prop where
  destination : t.gpr .r14 = VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset
  count : t.gpr .rax = VG.Proof.Argon2.X86_64.Initial.wordAt s blocksOffset * 128
  zero : t.gpr .rcx = 0
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clearSetup_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8) :
    WP isa clearSetupCode s (VG.Proof.Argon2.X86_64.MemoryInit.ClearSetup s) := by
  unfold clearSetupCode clearSetup
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.MemoryInit.clearHeader_ok s memoryRead blocksRead).mono ?_
  intro a ha
  refine (scale_ok a .rax 7).mono ?_
  intro b hb
  exact ⟨(hb.other _ (by decide)).trans ha.destination,
    by rw [hb.value, ha.count]; rfl,
    (hb.other _ (by decide)).trans ha.zero,
    fun r h1 h2 h3 => (hb.other r h2).trans (ha.other r h1 h2 h3),
    hb.mem.trans ha.mem, hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩

structure Cleared (s t : State) (memory : Addr) (blocks : Nat) : Prop where
  destination : t.gpr .r14 = memory + BitVec.ofNat 64 (1024 * blocks)
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = clearMem s.mem memory (128 * blocks)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clear_ok (s : State) (memory : Addr) (blocks : Nat) (lo : 1 ≤ blocks)
    (bound : 1024 * blocks < 2 ^ 64)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8)
    (memoryWord : VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset = memory)
    (blocksWord : VG.Proof.Argon2.X86_64.Initial.wordAt s blocksOffset = BitVec.ofNat 64 blocks)
    (cover : Covers [⟨memory, 1024 * blocks⟩] s.wr) :
    WP isa clear s fun t => VG.Proof.Argon2.X86_64.MemoryInit.Cleared s t memory blocks := by
  unfold clear
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.clearSetup_ok s memoryRead blocksRead).mono ?_)
  intro b hb
  have count : b.gpr .rax = BitVec.ofNat 64 (128 * blocks) := by
    rw [hb.count, blocksWord, show (128 : Addr) = BitVec.ofNat 64 128 from rfl,
      ← BitVec.ofNat_mul, Nat.mul_comm]
  have dst : b.gpr .r14 = memory := hb.destination.trans memoryWord
  have zero := hb.zero
  have mem := hb.mem
  have rd := hb.rd
  have wr := hb.wr
  have other := hb.other
  refine (clearLoop_ok b memory (128 * blocks) (by omega) (by omega) dst count zero ?_).mono ?_
  · intro j hj
    rw [wr]
    exact cover _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · intro t ht
    refine ⟨?_, fun r h1 h2 h3 => (ht.other r h2 h1).trans (other r h1 h2 h3), ?_,
      ht.rd.trans rd, ht.wr.trans wr⟩
    · rw [ht.destination, show 8 * (128 * blocks) = 1024 * blocks by omega]
    · rw [ht.mem, mem]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Set up the public lane loop after matrix clearing -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure LanesHeader (s t : State) : Prop where
  destination : t.gpr .r14 = VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset
  lane : t.gpr .r12 = 0
  remaining : t.gpr .r15 = VG.Proof.Argon2.X86_64.Initial.wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lanesHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8) :
    WP isa (.block lanesHeader) s (VG.Proof.Argon2.X86_64.MemoryInit.LanesHeader s) := by
  apply WP.of_runBlock
  simp only [lanesHeader, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.setReg32, HPrime.ea_at, memoryOffset, VG.Impl.Argon2.X86_64.Initial.lanesOffset,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 232 = (232 : Addr) from rfl,
    show BitVec.ofNat 64 184 = (184 : Addr) from rfl,
    memoryRead, lanesRead, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

structure Setup (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  destination : t.gpr .r14 = memory
  lane : t.gpr .r12 = 0
  remaining : t.gpr .r15 = BitVec.ofNat 64 lanes
  stride : t.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → r ≠ .r13 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lanesSetup_ok (s : State) (memory : Addr) (lanes q : Nat)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8)
    (memoryWord : VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset = memory)
    (lanesWord : VG.Proof.Argon2.X86_64.Initial.wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (laneLength : s.gpr .r13 = BitVec.ofNat 64 q) :
    WP isa (.block lanesSetup) s fun t => VG.Proof.Argon2.X86_64.MemoryInit.Setup s t memory lanes q := by
  unfold lanesSetup
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.MemoryInit.lanesHeader_ok s memoryRead lanesRead).mono ?_
  intro a ha
  refine (scale_ok a .r13 10).mono ?_
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => (ht.other r h4).trans (ha.other r h1 h2 h3),
    ht.mem.trans ha.mem, ht.rd.trans ha.rd, ht.wr.trans ha.wr⟩
  · rw [ht.other .r14 (by decide), ha.destination, memoryWord]
  · rw [ht.other .r12 (by decide), ha.lane]
  · rw [ht.other .r15 (by decide), ha.remaining, lanesWord]
  · rw [ht.value, ha.other .r13 (by decide) (by decide) (by decide), laneLength,
      ← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitLoop`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitFrame`. -/
section
/-! # Effects allowed across the complete lane loop -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Spec.Blake2 (bytesAt)

def keptRegs : List Reg := [.rbp, .rbx, .rsp, .r13]

structure Keeps (s t : State) (memory : Addr) (bytes : Nat) : Prop where
  regs : ∀ r ∈ VG.Proof.Argon2.X86_64.MemoryInit.keptRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, bytes⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem Keeps.rbp {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes) :
    t.gpr .rbp = s.gpr .rbp := h.regs _ (by decide)
theorem Keeps.rbx {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes) :
    t.gpr .rbx = s.gpr .rbx := h.regs _ (by decide)
theorem Keeps.rsp {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes) :
    t.gpr .rsp = s.gpr .rsp := h.regs _ (by decide)

theorem Keeps.refl (s : State) (memory : Addr) (bytes : Nat) : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s s memory bytes :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {s t u : State} {memory : Addr} {bytes : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes) (k : VG.Proof.Argon2.X86_64.MemoryInit.Keeps t u memory bytes) : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s u memory bytes :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.rbx, h.rsp, h.rbp] using k.frame)⟩

theorem Space.keeps {s t : State} {memory : Addr} {bytes : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory bytes) (k : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes) : VG.Proof.Argon2.X86_64.MemoryInit.Space t memory bytes :=
  h.same k.wr k.rbp k.rbx k.rsp

theorem Keeps.h0 {s t : State} {memory : Addr} {bytes : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes) (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory bytes) :
    bytesAt t.mem (t.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
  rw [h.rbp]
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .rbp, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact space.frameMatrix.sub_left (Region.sub_prefix (by decide))
  · exact space.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact space.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem LaneDone.keeps {s t : State} (memory : Addr) (bytes d : Nat)
    (h : VG.Proof.Argon2.X86_64.MemoryInit.LaneDone s t) (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d)
    (bound : d + 2048 ≤ bytes) : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s t memory bytes := by
  refine ⟨?_, h.rd, h.wr, ?_⟩
  · intro r hr
    have facts : ∀ r ∈ VG.Proof.Argon2.X86_64.MemoryInit.keptRegs, r ∈ calleeSaved ∧ r ≠ .r14 ∧ r ≠ .r12 ∧ r ≠ .r15 := by decide
    obtain ⟨cs, h14, h12, h15⟩ := facts r hr
    exact h.regs r cs h14 h12 h15
  · apply h.frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [dst]; exact Offset.sub_base _ bound⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))), fun _ h => h⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Termination and correctness of the all-lanes initialization loop -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopI (s₀ : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte) (s : State) : Prop where
  bound : j ≤ lanes
  destination : s.gpr .r14 = memory + BitVec.ofNat 64 (1024 * (j * q))
  lane : s.gpr .r12 = BitVec.ofNat 64 j
  remaining : s.gpr .r15 = BitVec.ofNat 64 (lanes - j)
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  keeps : VG.Proof.Argon2.X86_64.MemoryInit.Keeps s₀ s memory (1024 * (lanes * q))
  initialized : VG.Proof.Argon2.X86_64.MemoryInit.Initialized s.mem memory lanes q j h0
  hash : bytesAt s.mem (s.gpr .rbp) 64 = h0

theorem lane_step (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₀ s : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte)
    (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s₀ memory (1024 * (lanes * q))) (hj : j < lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (h : VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₀ memory lanes q j h0 s) :
    WP isa (lane name (HPrime.hash v)) s fun t =>
      VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₀ memory lanes q (j + 1) h0 t ∧
      t.zf = some (decide (lanes - (j + 1) = 0)) := by
  have spaceS := space.keeps h.keeps
  have endBound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  refine (VG.Proof.Argon2.X86_64.MemoryInit.lane_ok v name s memory (1024 * (lanes * q)) (1024 * (j * q))
    spaceS h.destination endBound).mono ?_
  intro t ht
  have kt := ht.keeps memory _ _ h.destination endBound
  have nextCount : BitVec.ofNat 64 (lanes - j) - 1 = BitVec.ofNat 64 (lanes - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₀ memory lanes q (j + 1) h0 t := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, h.keeps.trans kt,
      VG.Proof.Argon2.X86_64.MemoryInit.initialized_lane memory lanes q j h0 spaceS hq hj lanesBound h.destination h.lane
        h.hash h.initialized ht, (kt.h0 spaceS).trans h.hash⟩
    · rw [ht.destination, h.destination, h.stride, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_mul, Nat.one_mul, Nat.mul_add]
    · rw [ht.lane, h.lane, BitVec.ofNat_add]; rfl
    · rw [ht.remaining, h.remaining, nextCount]
    · exact (kt.regs .r13 (by decide)).trans h.stride
  have zf : t.zf = some (decide (lanes - (j + 1) = 0)) := by
    rw [ht.zf, h.remaining, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lanes - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  exact ⟨next, zf⟩


theorem lanesLoop_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₀ : State) (memory : Addr) (lanes q : Nat) (h0 : List Byte)
    (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s₀ memory (1024 * (lanes * q))) (lo : 1 ≤ lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (dst : s₀.gpr .r14 = memory) (laneReg : s₀.gpr .r12 = 0)
    (remaining : s₀.gpr .r15 = BitVec.ofNat 64 lanes)
    (stride : s₀.gpr .r13 = BitVec.ofNat 64 (1024 * q))
    (initialized : VG.Proof.Argon2.X86_64.MemoryInit.Initialized s₀.mem memory lanes q 0 h0)
    (hash : bytesAt s₀.mem (s₀.gpr .rbp) 64 = h0) :
    WP isa (.loop (lane name (HPrime.hash v)) .ne) s₀ (VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₀ memory lanes q lanes h0) := by
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = lanes - j ∧ j < lanes ∧ VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₀ memory lanes q j h0 s)
    ?_ lanes s₀ ⟨0, by omega, lo, by omega, by simpa using dst, laneReg,
      by simpa only [Nat.sub_zero] using remaining, stride, Keeps.refl _ _ _, initialized, hash⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine (VG.Proof.Argon2.X86_64.MemoryInit.lane_step v name s₀ s memory lanes q j h0 space hj lanesBound hq h).mono ?_
  intro t ⟨next, zf⟩
  by_cases done : j + 1 = lanes
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, show lanes - (j + 1) = 0 by omega, decide_true,
      Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, lanes - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, zf, show lanes - (j + 1) ≠ 0 by omega, decide_false,
      Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInit`. -/
section
/-! # Functional correctness of complete memory initialization -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)
open VG.Spec.Blake2 (bytesAt)

theorem Cleared.frame {s t : State} {memory : Addr} {blocks : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Cleared s t memory blocks) (bound : 1024 * blocks < 2 ^ 64) :
    Frame [⟨memory, 1024 * blocks⟩] s.mem t.mem := by
  rw [h.mem]
  simpa only [show 8 * (128 * blocks) = 1024 * blocks by omega] using
    clearMem_frame s.mem memory (128 * blocks) (by omega)

theorem Cleared.word {s t : State} {memory : Addr} {blocks d : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Cleared s t memory blocks) (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory (1024 * blocks))
    (offset : d + 8 ≤ 272) : VG.Proof.Argon2.X86_64.Initial.wordAt t d = VG.Proof.Argon2.X86_64.Initial.wordAt s d := by
  unfold VG.Proof.Argon2.X86_64.Initial.wordAt
  rw [h.other .rbp (by decide) (by decide) (by decide)]
  apply (h.frame space.bound).readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ offset (by omega)) ?_ (by decide)
  intro r hr; simp only [List.mem_singleton] at hr; subst r
  exact space.frameMatrix

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (hq : 2 ≤ q)
    (lanesBound : lanes < 2 ^ 64) (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory (1024 * (lanes * q)))
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8)
    (memoryWord : VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset = memory)
    (lanesWord : VG.Proof.Argon2.X86_64.Initial.wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (blocksWord : VG.Proof.Argon2.X86_64.Initial.wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q))
    (laneLength : s.gpr .r13 = BitVec.ofNat 64 q) :
    WP isa (VG.Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)) s fun t =>
      VG.Proof.Argon2.X86_64.MemoryInit.Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .rbp) 64) ∧
      t.gpr .rbp = s.gpr .rbp ∧ t.gpr .rbx = s.gpr .rbx ∧ t.gpr .rsp = s.gpr .rsp ∧
      t.gpr .r13 = BitVec.ofNat 64 (1024 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem := by
  unfold VG.Impl.Argon2.X86_64.MemoryInit.code lanesSetupCode
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.clear_ok s memory (lanes * q) blocksPositive space.bound memoryRead
    blocksRead memoryWord blocksWord space.matrix).mono ?_)
  intro a ha
  have bpA := ha.other .rbp (by decide) (by decide) (by decide)
  have bxA := ha.other .rbx (by decide) (by decide) (by decide)
  have spA := ha.other .rsp (by decide) (by decide) (by decide)
  have spaceA := space.same ha.wr bpA bxA spA
  have hashA : bytesAt a.mem (a.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
    rw [bpA]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact (ha.frame space.bound).bytes (R := ⟨s.gpr .rbp, 64⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact space.frameMatrix.sub_left (Region.sub_prefix (by decide)))
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine WP.seq ((VG.Proof.Argon2.X86_64.MemoryInit.lanesSetup_ok a memory lanes q
    (by rw [ha.rd, ha.wr, bpA]; exact memoryRead)
    (by rw [ha.rd, ha.wr, bpA]; exact lanesRead)
    ((ha.word space (by decide)).trans memoryWord)
    ((ha.word space (by decide)).trans lanesWord)
    ((ha.other .r13 (by decide) (by decide) (by decide)).trans laneLength)).mono ?_)
  intro b hb
  have bpB := hb.other .rbp (by decide) (by decide) (by decide) (by decide)
  have bxB := hb.other .rbx (by decide) (by decide) (by decide) (by decide)
  have spB := hb.other .rsp (by decide) (by decide) (by decide) (by decide)
  have spaceB := spaceA.same hb.wr bpB bxB spB
  refine (VG.Proof.Argon2.X86_64.MemoryInit.lanesLoop_ok v name b memory lanes q (bytesAt s.mem (s.gpr .rbp) 64)
    spaceB lo lanesBound hq hb.destination hb.lane hb.remaining hb.stride ?_ ?_).mono ?_
  · rw [hb.mem, ha.mem]
    exact VG.Proof.Argon2.X86_64.MemoryInit.initialized_zero s.mem memory lanes q space.bound _
  · rw [hb.mem, bpB]; exact hashA
  · intro t ht
    refine ⟨ht.initialized, ht.keeps.rbp.trans (bpB.trans bpA),
      ht.keeps.rbx.trans (bxB.trans bxA), ht.keeps.rsp.trans (spB.trans spA),
      (ht.keeps.regs .r13 (by decide)).trans hb.stride, ht.keeps.rd.trans (hb.rd.trans ha.rd), ht.keeps.wr.trans (hb.wr.trans ha.wr), ?_⟩
    have fb : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem b.mem := by
      rw [hb.mem]
      exact (ha.frame space.bound).mono (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact List.mem_cons_self ..)
    apply fb.trans
    have f := ht.keeps.frame
    rw [bpB, bpA, bxB, bxA, spB, spA] at f
    exact f

/-- Every cell agrees with the reviewed initialization spec, in lane-major order. -/
theorem Initialized.spec {m : Mem} {base : Addr} {p : Spec.Argon2.Params}
    {h0 : List Byte} (hl : 0 < p.lanes) (hq : 0 < p.laneLen)
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Initialized m base p.lanes p.laneLen p.lanes h0)
    (k : Nat) (hk : k < p.blocks) :
    Spec.Argon2.blockAt m (base + BitVec.ofNat 64 (1024 * k)) =
      (Spec.Argon2.initMemory p h0).memory[k]'(by
        rw [Proof.Argon2.initMemory_size]; exact hk) := by
  have blocks := Proof.Argon2.blocks_lanes p hl
  have lane : k / p.laneLen < p.lanes := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    simpa only [blocks] using hk
  have cell := h (k / p.laneLen) lane (k % p.laneLen) (Nat.mod_lt _ hq)
  rw [Nat.mul_comm (k / p.laneLen) p.laneLen, Nat.div_add_mod] at cell
  simp only [lane, true_and] at cell
  rw [Proof.Argon2.initMemory_cell p h0 k hk]
  exact cell

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitRepresent`. -/
section
/-! Memory initialization establishes the shared matrix representation invariant. -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.Spec.Argon2

theorem Initialized.represents {m : Mem} {base : Addr} {p : Params} {h0 : List Byte}
    (positive : 0 < p.lanes) (lanePositive : 0 < p.laneLen)
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Initialized m base p.lanes p.laneLen p.lanes h0) :
    Proof.Argon2.Represents m base p.blocks (initMemory p h0).memory := by
  refine ⟨Proof.Argon2.initMemory_size p h0, ?_⟩
  intro k hk
  rw [Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk), Option.getD_some]
  unfold Proof.Argon2.matrixCell
  rw [Nat.mul_comm k 1024]
  exact h.spec positive lanePositive k hk

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitBlockCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitCallCT`. -/
section
/-! # Initialization's H′ calls leak only their public argument registers -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (code)

theorem hPrime_call_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → VG.Proof.Argon2.X86_64.MemoryInit.CallReady s ∧ VG.Proof.Argon2.X86_64.MemoryInit.CallReady t ∧
      s.gpr .rsi = 72 ∧ t.gpr .rsi = 72 ∧ s.gpr .rcx = 1024 ∧ t.gpr .rcx = 1024 ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rdx = t.gpr .rdx ∧
      s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call name (VG.Impl.Argon2.X86_64.HPrime.code (HPrime.hash v))) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := VG.Proof.Argon2.X86_64.MemoryInit.hPrime_call_hyps s hs ls os
  obtain ⟨pt, ct, wt⟩ := VG.Proof.Argon2.X86_64.MemoryInit.hPrime_call_hyps t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx ∧
    s.callEntry.gpr .r8 = t.callEntry.gpr .r8 ∧
    s.callEntry.gpr .rsp = t.callEntry.gpr .rsp
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, congrArg (· - 8) sp⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Public registers survive each initialization H′ call -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

def AgreeSaved (s t : State) : Prop := ∀ r ∈ calleeSaved, s.gpr r = t.gpr r

theorem blockArgs_rel (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved (.block (blockArgs column)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) check

theorem block_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.X86_64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t)
      (VG.Impl.Argon2.X86_64.MemoryInit.block name (HPrime.hash v) column) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved := by
  let P := fun s t => VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.X86_64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t
  have args := ((VG.Proof.Argon2.X86_64.MemoryInit.blockArgs_rel column ct).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp => by
      exact ⟨VG.Proof.Argon2.X86_64.MemoryInit.blockArgs_ok s column (hp.1.prefix 64 (by decide)) (hp.1.prefix 68 (by decide)),
        VG.Proof.Argon2.X86_64.MemoryInit.blockArgs_ok t column (hp.2.1.prefix 64 (by decide)) (hp.2.1.prefix 68 (by decide))⟩)
  have call := VG.Proof.Argon2.X86_64.MemoryInit.hPrime_call_rel v name (P := fun a b =>
      True ∧ ∃ s t, P s t ∧ VG.Proof.Argon2.X86_64.MemoryInit.BlockArgs s a column ∧ VG.Proof.Argon2.X86_64.MemoryInit.BlockArgs t b column) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.ready hp.1, hb.ready hp.2.1, ha.inputLength, hb.inputLength,
      ha.outputLength, hb.outputLength, ?_, ?_, ?_, ?_⟩
    · exact ha.input.trans ((hp.2.2 .rbp (by decide)).trans hb.input.symm)
    · exact ha.output.trans ((hp.2.2 .r14 (by decide)).trans hb.output.symm)
    · exact ha.work.trans ((hp.2.2 .rbx (by decide)).trans hb.work.symm)
    · exact (ha.regs .rsp (by decide)).trans
        ((hp.2.2 .rsp (by decide)).trans (hb.regs .rsp (by decide)).symm))
  have full := (args.seq call).wpDep (fun s t hp =>
    ⟨VG.Proof.Argon2.X86_64.MemoryInit.block_ok v name s column hp.1, VG.Proof.Argon2.X86_64.MemoryInit.block_ok v name t column hp.2.1⟩)
  exact full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    intro r hr
    exact (ha.regs r hr).trans ((hp.2.2 r hr).trans (hb.regs r hr).symm))

theorem blocks_rel (v : Proof.Blake2.X86_64.Backend) (name : String) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.X86_64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t)
      (VG.Impl.Argon2.X86_64.MemoryInit.block name (HPrime.hash v) 0) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved ∧
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.X86_64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t)
      (VG.Impl.Argon2.X86_64.MemoryInit.block name (HPrime.hash v) 1) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved :=
  ⟨VG.Proof.Argon2.X86_64.MemoryInit.block_rel v name 0 ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.X86_64.MemoryInit.block_rel v name 1 ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitLoopCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitLaneCT`. -/
section
/-! # The two leading blocks of a lane have a public execution trace -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

structure LaneReady (memory : Addr) (bytes d : Nat) (s : State) : Prop where
  space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory bytes
  destination : s.gpr .r14 = memory + BitVec.ofNat 64 d

def RelatedLane (memory : Addr) (bytes d : Nat) (s t : State) : Prop :=
  VG.Proof.Argon2.X86_64.MemoryInit.LaneReady memory bytes d s ∧ VG.Proof.Argon2.X86_64.MemoryInit.LaneReady memory bytes d t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t

theorem BlockDone.laneReady {s t : State} {column : Nat} {memory : Addr} {bytes d : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.BlockDone s t column) (ready : VG.Proof.Argon2.X86_64.MemoryInit.LaneReady memory bytes d s) :
    VG.Proof.Argon2.X86_64.MemoryInit.LaneReady memory bytes d t :=
  ⟨ready.space.same h.wr (h.regs .rbp (by decide)) (h.regs .rbx (by decide))
    (h.regs .rsp (by decide)), (h.regs .r14 (by decide)).trans ready.destination⟩

theorem block_lane_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true)
    (memory : Addr) (bytes d : Nat) (bound : d + 1024 ≤ bytes) :
    RelCT isa (VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes d) (VG.Impl.Argon2.X86_64.MemoryInit.block name (HPrime.hash v) column)
      (VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes d) := by
  have h := ((VG.Proof.Argon2.X86_64.MemoryInit.block_rel v name column ct).mono
    (P' := VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes d) (fun _ _ hp =>
      ⟨hp.1.space.blockReady hp.1.destination bound,
        hp.2.1.space.blockReady hp.2.1.destination bound, hp.2.2⟩)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨VG.Proof.Argon2.X86_64.MemoryInit.block_ok v name s column (hp.1.space.blockReady hp.1.destination bound),
        VG.Proof.Argon2.X86_64.MemoryInit.block_ok v name t column (hp.2.1.space.blockReady hp.2.1.destination bound)⟩)
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ha.laneReady hp.1, hb.laneReady hp.2.1, pub⟩)

theorem advance_rel : RelCT isa VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved
    (.block [.alu .add .r14 (.imm 1024)]) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) calleeSaved
  taint_decide

theorem advance_lane_rel (memory : Addr) (bytes d : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes d) (.block [.alu .add .r14 (.imm 1024)])
      (VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes (d + 1024)) := by
  have h := (advance_rel.mono (P' := VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes d)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.X86_64.MemoryInit.advance_ok s, VG.Proof.Argon2.X86_64.MemoryInit.advance_ok t⟩)
  have ready {s t : State} (h : Advanced s t) (hs : VG.Proof.Argon2.X86_64.MemoryInit.LaneReady memory bytes d s) :
      VG.Proof.Argon2.X86_64.MemoryInit.LaneReady memory bytes (d + 1024) t := by
    refine ⟨hs.space.same h.wr (h.other .rbp (by decide))
      (h.other .rbx (by decide)) (h.other .rsp (by decide)), ?_⟩
    rw [h.destination, hs.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ready ha hp.1, ready hb hp.2.1, pub⟩)

theorem laneEnd_rel : RelCT isa VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved
    (.block [.alu .add .r14 (.reg .r13), .alu .sub .r14 (.imm 1024),
      .alu .add .r12 (.imm 1), .alu .sub .r15 (.imm 1)]) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) calleeSaved
  taint_decide

theorem lane_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (bytes d : Nat) (bound : d + 2048 ≤ bytes) :
    RelCT isa (VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory bytes d) (lane name (HPrime.hash v)) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved := by
  exact (VG.Proof.Argon2.X86_64.MemoryInit.block_lane_rel v name 0 ⟨_, by taint_decide⟩ memory bytes d (by omega)).seq
    ((VG.Proof.Argon2.X86_64.MemoryInit.advance_lane_rel memory bytes d).seq
    ((VG.Proof.Argon2.X86_64.MemoryInit.block_lane_rel v name 1 ⟨_, by taint_decide⟩ memory bytes (d + 1024) (by omega)).seq
      (laneEnd_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h))))

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Both initialization loops count only pubNext matrix dimensions -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

theorem lanesLoop_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₁ s₂ : State) (memory : Addr) (lanes q : Nat) (h₁ h₂ : List Byte)
    (space₁ : VG.Proof.Argon2.X86_64.MemoryInit.Space s₁ memory (1024 * (lanes * q)))
    (space₂ : VG.Proof.Argon2.X86_64.MemoryInit.Space s₂ memory (1024 * (lanes * q)))
    (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₁ memory lanes q 0 h₁ s ∧
      VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₂ memory lanes q 0 h₂ t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t)
      (.loop (lane name (HPrime.hash v)) .ne) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved := by
  let I := fun n s t => ∃ j, n = lanes - j ∧ j < lanes ∧
    VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₁ memory lanes q j h₁ s ∧ VG.Proof.Argon2.X86_64.MemoryInit.LoopI s₂ memory lanes q j h₂ t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t
  have steps : ∀ n, RelCT isa (I n) (lane name (HPrime.hash v)) fun a b =>
      isa.eval .ne a = isa.eval .ne b ∧
      (isa.eval .ne a = some false → VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved a b) ∧
      (isa.eval .ne a = some true → ∃ m < n, I m a b) := by
    intro n s t trace₁ trace₂ a b hp e₁ e₂
    obtain ⟨j, rfl, hj, hs, ht, pub⟩ := hp
    have bound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
      have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    have related : VG.Proof.Argon2.X86_64.MemoryInit.RelatedLane memory (1024 * (lanes * q)) (1024 * (j * q)) s t :=
      ⟨⟨space₁.keeps hs.keeps, hs.destination⟩,
        ⟨space₂.keeps ht.keeps, ht.destination⟩, pub⟩
    obtain ⟨trace, pubNext⟩ := VG.Proof.Argon2.X86_64.MemoryInit.lane_rel v name memory _ _ bound _ _ _ _ _ _ related e₁ e₂
    obtain ⟨_, a', ea, ha⟩ := VG.Proof.Argon2.X86_64.MemoryInit.lane_step v name s₁ s memory lanes q j h₁
      space₁ hj lanesBound hq hs
    obtain ⟨_, b', eb, hb⟩ := VG.Proof.Argon2.X86_64.MemoryInit.lane_step v name s₂ t memory lanes q j h₂
      space₂ hj lanesBound hq ht
    obtain ⟨-, rfl⟩ := Exec.det e₁ ea
    obtain ⟨-, rfl⟩ := Exec.det e₂ eb
    refine ⟨trace, ?_, fun _ => pubNext, ?_⟩
    · simp only [eval, ha.2, hb.2]
    · intro taken
      have remaining : lanes - (j + 1) ≠ 0 := by
        intro zero
        simp only [eval, ha.2, zero, decide_true, Option.map_some,
          Bool.not_true, Option.some.injEq, Bool.false_eq_true] at taken
      exact ⟨lanes - (j + 1), by omega, j + 1, rfl, by omega, ha.1, hb.1, pubNext⟩
  exact (RelCT.loop I steps lanes).mono (fun _ _ hp =>
    ⟨0, by omega, lo, hp.1, hp.2.1, hp.2.2⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitDone`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitClearCT`. -/
section
/-! # Matrix clearing uses only public addresses and the public allocation size -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure Ready (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory (1024 * (lanes * q))
  memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8
  lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8
  blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8
  memoryWord : VG.Proof.Argon2.X86_64.Initial.wordAt s memoryOffset = memory
  lanesWord : VG.Proof.Argon2.X86_64.Initial.wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes
  blocksWord : VG.Proof.Argon2.X86_64.Initial.wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q)
  laneLength : s.gpr .r13 = BitVec.ofNat 64 q

def publicBases : List Reg := [.rbp, .rbx, .rsp, .r13]

def AgreeBases (s t : State) : Prop := ∀ r ∈ VG.Proof.Argon2.X86_64.MemoryInit.publicBases, s.gpr r = t.gpr r

theorem clearSetup_rel : RelCT isa VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases clearSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Argon2.X86_64.MemoryInit.publicBases)
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem clearLoop_rel : RelCT isa
    (fun s t => VG.X86_64.Taint.Agree (Taint.ofRegs (.rax :: .r14 :: VG.Proof.Argon2.X86_64.MemoryInit.publicBases)) s t)
    (.loop (.block clearWord) .ne) VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases := by
  apply RelCT.taintRegs (τ := Taint.ofRegs (.rax :: .r14 :: VG.Proof.Argon2.X86_64.MemoryInit.publicBases))
    (fun _ _ h => h) VG.Proof.Argon2.X86_64.MemoryInit.publicBases
  taint_decide

theorem clear_rel (memory : Addr) (lanes q : Nat) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q s ∧ VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases s t)
      clear VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases := by
  let P := fun s t => VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q s ∧ VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases s t
  have prep := (clearSetup_rel.mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨VG.Proof.Argon2.X86_64.MemoryInit.clearSetup_ok s h.1.memoryRead h.1.blocksRead,
        VG.Proof.Argon2.X86_64.MemoryInit.clearSetup_ok t h.2.1.memoryRead h.2.1.blocksRead⟩)
  refine prep.seq (clearLoop_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rw [ha.count, hb.count, hp.1.blocksWord, hp.2.1.blocksWord]
  · rw [ha.destination, hb.destination, hp.1.memoryWord, hp.2.1.memoryWord]
  · have excluded : ∀ r ∈ VG.Proof.Argon2.X86_64.MemoryInit.publicBases, r ≠ .r14 ∧ r ≠ .rax ∧ r ≠ .rcx := by decide
    have hn := excluded r hr
    exact (ha.other r hn.1 hn.2.1 hn.2.2).trans
      ((hp.2.2 r hr).trans (hb.other r hn.1 hn.2.1 hn.2.2).symm)

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitCT`. -/
section
/-! # The complete memory initialization trace depends only on public parameters -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopReady (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory (1024 * (lanes * q))
  initialized : VG.Proof.Argon2.X86_64.MemoryInit.Initialized s.mem memory lanes q 0 (bytesAt s.mem (s.gpr .rbp) 64)
  destination : s.gpr .r14 = memory
  lane : s.gpr .r12 = 0
  remaining : s.gpr .r15 = BitVec.ofNat 64 lanes
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * q)

theorem Cleared.ready {s t : State} {memory : Addr} {lanes q : Nat}
    (h : VG.Proof.Argon2.X86_64.MemoryInit.Cleared s t memory (lanes * q)) (hs : VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q s) :
    VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q t := by
  have bp := h.other .rbp (by decide) (by decide) (by decide)
  have bx := h.other .rbx (by decide) (by decide) (by decide)
  have sp := h.other .rsp (by decide) (by decide) (by decide)
  refine ⟨hs.space.same h.wr bp bx sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.rd, h.wr, bp]; exact hs.memoryRead
  · rw [h.rd, h.wr, bp]; exact hs.lanesRead
  · rw [h.rd, h.wr, bp]; exact hs.blocksRead
  · exact (h.word hs.space (by decide)).trans hs.memoryWord
  · exact (h.word hs.space (by decide)).trans hs.lanesWord
  · exact (h.word hs.space (by decide)).trans hs.blocksWord
  · exact (h.other .r13 (by decide) (by decide) (by decide)).trans hs.laneLength

theorem Setup.loopReady {s a b : State} {memory : Addr} {lanes q : Nat}
    (hs : VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q s) (ha : VG.Proof.Argon2.X86_64.MemoryInit.Cleared s a memory (lanes * q))
    (hb : VG.Proof.Argon2.X86_64.MemoryInit.Setup a b memory lanes q) : VG.Proof.Argon2.X86_64.MemoryInit.LoopReady memory lanes q b := by
  have ready := ha.ready hs
  refine ⟨ready.space.same hb.wr (hb.other .rbp (by decide) (by decide) (by decide) (by decide))
    (hb.other .rbx (by decide) (by decide) (by decide) (by decide))
    (hb.other .rsp (by decide) (by decide) (by decide) (by decide)), ?_,
    hb.destination, hb.lane, hb.remaining, hb.stride⟩
  rw [hb.mem, ha.mem]
  exact VG.Proof.Argon2.X86_64.MemoryInit.initialized_zero s.mem memory lanes q hs.space.bound _

theorem lanesSetup_rel : RelCT isa VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases lanesSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Argon2.X86_64.MemoryInit.publicBases)
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem Setup.agree {s t a b : State} {memory : Addr} {lanes q : Nat}
    (ha : VG.Proof.Argon2.X86_64.MemoryInit.Setup s a memory lanes q) (hb : VG.Proof.Argon2.X86_64.MemoryInit.Setup t b memory lanes q)
    (hp : VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases s t) : VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved a b := by
  intro r hr
  by_cases h14 : r = .r14
  · subst r; exact ha.destination.trans hb.destination.symm
  by_cases h12 : r = .r12
  · subst r; exact ha.lane.trans hb.lane.symm
  by_cases h15 : r = .r15
  · subst r; exact ha.remaining.trans hb.remaining.symm
  by_cases h13 : r = .r13
  · subst r; exact ha.stride.trans hb.stride.symm
  have included : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → r ≠ .r13 →
      r ∈ VG.Proof.Argon2.X86_64.MemoryInit.publicBases := by decide
  exact (ha.other r h14 h12 h15 h13).trans
    ((hp r (included r hr h14 h12 h15 h13)).trans (hb.other r h14 h12 h15 h13).symm)

theorem lanesLoop_ready_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    RelCT isa (fun s t => VG.Proof.Argon2.X86_64.MemoryInit.LoopReady memory lanes q s ∧ VG.Proof.Argon2.X86_64.MemoryInit.LoopReady memory lanes q t ∧
      VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved s t) (.loop (lane name (HPrime.hash v)) .ne) VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved := by
  intro s t ts tt a b hp es et
  have initial {s : State} (h : VG.Proof.Argon2.X86_64.MemoryInit.LoopReady memory lanes q s) :
      VG.Proof.Argon2.X86_64.MemoryInit.LoopI s memory lanes q 0 (bytesAt s.mem (s.gpr .rbp) 64) s :=
    ⟨by omega, by simpa using h.destination, h.lane,
      by simpa only [Nat.sub_zero] using h.remaining, h.stride, Keeps.refl _ _ _,
      h.initialized, rfl⟩
  exact VG.Proof.Argon2.X86_64.MemoryInit.lanesLoop_rel v name s t memory lanes q _ _ hp.1.space hp.2.1.space lo
    lanesBound hq _ _ _ _ _ _ ⟨initial hp.1, initial hp.2.1, hp.2.2⟩ es et

theorem code_ct (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    ConstantTime isa (VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q) VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases (VG.Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)) := by
  let P := fun s t => VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q s ∧ VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q t ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases s t
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  have cleared := (VG.Proof.Argon2.X86_64.MemoryInit.clear_rel memory lanes q).wpDep (fun s t hp =>
    ⟨VG.Proof.Argon2.X86_64.MemoryInit.clear_ok s memory (lanes * q) blocksPositive hp.1.space.bound hp.1.memoryRead
        hp.1.blocksRead hp.1.memoryWord hp.1.blocksWord hp.1.space.matrix,
      VG.Proof.Argon2.X86_64.MemoryInit.clear_ok t memory (lanes * q) blocksPositive hp.2.1.space.bound hp.2.1.memoryRead
        hp.2.1.blocksRead hp.2.1.memoryWord hp.2.1.blocksWord hp.2.1.space.matrix⟩)
  let R := fun a b => VG.Proof.Argon2.X86_64.MemoryInit.AgreeBases a b ∧ ∃ s t, P s t ∧
    VG.Proof.Argon2.X86_64.MemoryInit.Cleared s a memory (lanes * q) ∧ VG.Proof.Argon2.X86_64.MemoryInit.Cleared t b memory (lanes * q)
  have setup := (lanesSetup_rel.mono (P' := R) (fun _ _ h => h.1)
    (fun _ _ h => h)).wpDep (F := fun a b => VG.Proof.Argon2.X86_64.MemoryInit.Setup a b memory lanes q) (by
    intro a b hp
    obtain ⟨_, s, t, hst, ha, hb⟩ := hp
    have ra := ha.ready hst.1
    have rb := hb.ready hst.2.1
    exact ⟨VG.Proof.Argon2.X86_64.MemoryInit.lanesSetup_ok a memory lanes q ra.memoryRead ra.lanesRead ra.memoryWord
        ra.lanesWord ra.laneLength,
      VG.Proof.Argon2.X86_64.MemoryInit.lanesSetup_ok b memory lanes q rb.memoryRead rb.lanesRead rb.memoryWord
        rb.lanesWord rb.laneLength⟩)
  have prepared : RelCT isa R lanesSetupCode (fun a b =>
      VG.Proof.Argon2.X86_64.MemoryInit.LoopReady memory lanes q a ∧ VG.Proof.Argon2.X86_64.MemoryInit.LoopReady memory lanes q b ∧ VG.Proof.Argon2.X86_64.MemoryInit.AgreeSaved a b) := setup.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, c, d, hp, ha, hb⟩ := h
    obtain ⟨pub, s, t, hst, hc, hd⟩ := hp
    exact ⟨ha.loopReady hst.1 hc, hb.loopReady hst.2.1 hd, ha.agree hb pub⟩)
  exact (cleared.seq (prepared.seq (VG.Proof.Argon2.X86_64.MemoryInit.lanesLoop_ready_rel v name memory lanes q lo
    lanesBound hq))).constantTime

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Initialization retains its byte stride and every public frame word outside its lane suffix. -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  initialized : VG.Proof.Argon2.X86_64.MemoryInit.Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .rbp) 64)
  bp : t.gpr .rbp = s.gpr .rbp
  bx : t.gpr .rbx = s.gpr .rbx
  sp : t.gpr .rsp = s.gpr .rsp
  stride : t.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem complete_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (memory : Addr) (lanes q : Nat) (ready : VG.Proof.Argon2.X86_64.MemoryInit.Ready memory lanes q s)
    (positive : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (minimum : 2 ≤ q) :
    WP isa (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.MemoryInit.Done s · memory lanes q) :=
  (VG.Proof.Argon2.X86_64.MemoryInit.code_ok v name s memory lanes q positive minimum lanesBound ready.space ready.memoryRead ready.lanesRead
    ready.blocksRead ready.memoryWord ready.lanesWord ready.blocksWord ready.laneLength).mono
      (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)

theorem Done.frame_word {s t : State} {memory : Addr} {lanes q : Nat}
    (space : VG.Proof.Argon2.X86_64.MemoryInit.Space s memory (1024 * (lanes * q))) (done : VG.Proof.Argon2.X86_64.MemoryInit.Done s t memory lanes q)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 64 ∨ 72 ≤ d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64 := by
  rw [done.bp]
  have sub : Region.Sub ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact space.frameMatrix.sub_left sub
    · exact space.frameWork.sub_left sub
    · exact space.stackFrame.symm.sub_left sub
    · exact Offset.disjoint (s.gpr .rbp) separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.InitFillReady`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSetupReset`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSetupDimensions`. -/
section
/-! Initialization's byte stride gives exact block and segment counts without division instructions. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

theorem dimensions_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.FillSetup.dimensions) s fun t =>
    t.gpr .r12 = s.gpr .r13 >>> 10 ∧ t.gpr .r13 = s.gpr .r13 >>> 12 ∧ Divide.Keeps [.r12, .r13] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FillSetup.dimensions, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    show 1 ≤ (10 : Nat) ∧ (10 : Nat) ≤ 63 from by decide,
    show 1 ≤ (12 : Nat) ∧ (12 : Nat) ≤ 63 from by decide,
    and_self, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem stride_shift (q shift : Nat) (bound : 1024 * q < 2 ^ 64) :
    BitVec.ofNat 64 (1024 * q) >>> shift = BitVec.ofNat 64 ((1024 * q) / 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) bound)]

theorem dimensions_nat_ok (s : State) (p : Params) (bound : 1024 * p.laneLen < 2 ^ 64)
    (stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * p.laneLen)) :
    WP isa (.block Impl.Argon2.X86_64.FillSetup.dimensions) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 p.laneLen ∧ t.gpr .r13 = BitVec.ofNat 64 p.segmentLen ∧
      Divide.Keeps [.r12, .r13] s t := by
  refine (VG.Proof.Argon2.X86_64.FillSetup.dimensions_ok s).mono ?_
  rintro t ⟨lane, segment, keeps⟩
  refine ⟨?_, ?_, keeps⟩
  · rw [lane, stride, VG.Proof.Argon2.X86_64.FillSetup.stride_shift _ 10 bound]
    simp only [show 2 ^ 10 = 1024 from rfl, Nat.mul_div_cancel_left _ (by decide : 0 < 1024)]
  · rw [segment, stride, VG.Proof.Argon2.X86_64.FillSetup.stride_shift _ 12 bound]
    have div : 1024 * p.laneLen / 4096 = p.laneLen / 4 := by
      rw [show (4096 : Nat) = 1024 * 4 from rfl, Nat.mul_div_mul_left _ _ (by decide : 0 < 1024)]
    rw [show 2 ^ 12 = 4096 from rfl, div]
    rfl

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Reset public loop coordinates and only the pass word in the enclosing frame. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Reset (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (0 : Addr)
  lane : t.gpr .rbx = 0
  slice : t.gpr .r14 = 0
  regs : ∀ r, r ∉ [Reg.rax, .rbx, .r14] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem reset_ok (s : State) (write : InRegions s.wr (off (s.gpr .rbp) 0) 8) :
    WP isa (.block Impl.Argon2.X86_64.FillSetup.reset) s (VG.Proof.Argon2.X86_64.FillSetup.Reset s) := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FillSetup.reset, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    write, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

theorem Reset.pass {s t : State} (h : VG.Proof.Argon2.X86_64.FillSetup.Reset s t) : t.mem.readW (off (t.gpr .rbp) 0) 64 = 0 := by
  rw [h.mem, h.regs .rbp (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem Reset.frame {s t : State} (h : VG.Proof.Argon2.X86_64.FillSetup.Reset s t) : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (r := ⟨s.gpr .rbp, 8⟩) (by simp) _
    (by simpa only [off, BitVec.add_zero] using Region.contains_self (s.gpr .rbp) 8)

theorem Reset.read {s t : State} (h : VG.Proof.Argon2.X86_64.FillSetup.Reset s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.mem, h.regs .rbp (by decide)]
  exact Mem.readW_writeW_sep (w := 64) (w' := 64)
    (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Merged from `Proof.Argon2.X86_64.FillSetupFinish`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSetupEnvironment`. -/
section
/-! Initialization hands filling the reviewed dimensions and stable public frame words. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Environment (p : Params) (s : State) : Prop where
  parameters : FillContext.Parameters p 0 0 0
  passesBound : p.passes < 2 ^ 32
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  counterWrite : InRegions s.wr (off (s.gpr .rbp) 8) 8
  passWrite : InRegions s.wr (off (s.gpr .rbp) 0) 8
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Environment.of_state {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.FillSetup.Environment p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.X86_64.FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.passesBound, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.counterWrite
  · rw [wr, bp]; exact h.passWrite
  · rw [base, work]; exact h.matrixWork
  all_goals rw [mem, bp]
  · exact h.blocksWord
  · exact h.passesWord
  · exact h.variantWord
  · exact h.lanesWord

theorem Reset.header {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.FillSetup.Environment p s) (reset : VG.Proof.Argon2.X86_64.FillSetup.Reset s t)
    (laneLength : t.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentLength : t.gpr .r13 = BitVec.ofNat 64 p.segmentLen) : FillHeader.Ready p 0 0 0 t := by
  have bp := reset.regs .rbp (by decide)
  have sp := reset.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := reset.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := reset.read 248 (by decide) (by decide)
  refine ⟨h.layout.of_preserved bp sp base work reset.rd reset.wr, ?_, ?_, ?_, ?_, ?_, laneLength,
    segmentLength, (reset.read 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [reset.rd, reset.wr, bp]; exact h.addressLayout.frameRead
    · rw [reset.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [reset.rd, reset.wr, bp]; exact h.reads
  · rw [reset.wr, bp]; exact h.counterWrite
  · refine ⟨(s.mem.readW (off (s.gpr .rbp) 8) 64).toNat, reset.pass, reset.lane, reset.slice,
      (reset.read 240 (by decide) (by decide)).trans h.blocksWord,
      (reset.read 72 (by decide) (by decide)).trans h.passesWord,
      (reset.read 112 (by decide) (by decide)).trans h.variantWord, ?_⟩
    rw [reset.read 8 (by decide) (by decide)]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Merged from `Proof.Argon2.X86_64.FillSetup`. -/
section
/-! Establish the complete pass-loop invariant from memory initialization's byte stride. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  environment : VG.Proof.Argon2.X86_64.FillSetup.Environment p s
  bound : 1024 * p.laneLen < 2 ^ 64
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * p.laneLen)

structure Prepared (s t : State) (p : Params) : Prop where
  ready : FillIterations.Ready p 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  words : ∀ d, 8 ≤ d → d + 8 ≤ 272 →
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64

theorem code_ok (s : State) (p : Params) (h : VG.Proof.Argon2.X86_64.FillSetup.Ready p s) :
    WP isa Impl.Argon2.X86_64.FillSetup.code s (VG.Proof.Argon2.X86_64.FillSetup.Prepared s · p) := by
  unfold Impl.Argon2.X86_64.FillSetup.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillSetup.dimensions_nat_ok s p h.bound h.stride).mono ?_)
  rintro a ⟨laneLength, segmentLength, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
  have environment := h.environment.of_state bp sp keeps.mem keeps.rd keeps.wr
  refine (VG.Proof.Argon2.X86_64.FillSetup.reset_ok a environment.passWrite).mono ?_
  intro t reset
  have header := reset.header environment ((reset.regs .r12 (by decide)).trans laneLength)
    ((reset.regs .r13 (by decide)).trans segmentLength)
  have words (d : Nat) (lower : 8 ≤ d) (upper : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [reset.read d lower upper, keeps.mem, bp]
  refine ⟨⟨⟨environment.parameters, 0, 0, header⟩, environment.passesBound, ?_⟩,
    words 232 (by decide) (by decide), words 248 (by decide) (by decide), ?_,
    reset.rd.trans keeps.rd, reset.wr.trans keeps.wr, ?_, reset.mxcsr.trans keeps.mxcsr, words⟩
  · rw [reset.wr, reset.regs .rbp (by decide)]; exact environment.passWrite
  · intro r hr bx q g sl
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reset.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ne, bx, sl⟩)).trans
      (keeps.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨q, g⟩))
  · have frame := reset.frame
    rw [bp, keeps.mem] at frame; exact frame

theorem Prepared.represents {s t : State} {p : Params} (ready : VG.Proof.Argon2.X86_64.FillSetup.Ready p s) (done : VG.Proof.Argon2.X86_64.FillSetup.Prepared s t p)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [done.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame done.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.environment.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Region.sub_prefix (by decide))

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.FillSetup.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Filling setup retains the final-call layout and establishes the reduction dimensions. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

theorem Prepared.finish_ready {s t : State} {p : Params} (ready : VG.Proof.Argon2.X86_64.FillSetup.Ready p s) (done : VG.Proof.Argon2.X86_64.FillSetup.Prepared s t p)
    (outputReady : FinalOutput.Ready p s) (positive : 0 < p.passes) : FillFinish.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have base : ReductionState.matrix t = ReductionState.matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.words 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.words 248 (by decide) (by decide)
  obtain ⟨lane, slice, header⟩ := done.ready.filling.header
  have params := ready.environment.parameters
  refine ⟨done.ready, ⟨?_, ?_⟩, positive⟩
  · refine ⟨⟨params.lanesPositive, params.segment_bound.1, ?_, header.layout.frameRead 232 (by simp),
      header.layout.matrixWrite, header.layout.matrixFrame, header.laneLength⟩,
      params.lanesBound, header.layout.frameRead 184 (by simp), header.lanesWord⟩
    have blocks := Proof.Argon2.blocks_le_memory p
    have memory := params.memoryBound
    omega
  · refine ⟨outputReady.positive, outputReady.bound, ?_,
      (done.words 264 (by decide) (by decide)).trans outputReady.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact outputReady.reads
    · rw [base, done.rd, done.wr]; exact outputReady.input
    · rw [output, done.wr]; exact outputReady.outputWrite
    · rw [work, done.wr]; exact outputReady.workWrite
    · rw [base, work]; exact outputReady.inputWork
    · rw [output, work]; exact outputReady.outputWork
    · rw [sp, base]; exact outputReady.stackInput
    · rw [sp, output]; exact outputReady.stackOutput
    · rw [sp, work]; exact outputReady.stackWork

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Retain the filling environment and final-call layout across memory initialization. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  initializing : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen s
  environment : FillSetup.Environment p s
  output : FinalOutput.Ready p s
  positive : 0 < p.passes
  scratch : s.gpr .rbx = FinalOutput.work s

theorem initialized_environment {s t : State} {p : Params} (h : VG.Proof.Argon2.X86_64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.bp done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.bp]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.bp, work]; exact e.addressLayout.frameWork
    · rw [done.bp, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.bp]; exact e.reads
  · rw [done.wr, done.bp]; exact e.counterWrite
  · rw [done.wr, done.bp]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word h.initializing.space 240 (by decide) (Or.inr (by decide))).trans e.blocksWord
  · exact (done.frame_word h.initializing.space 72 (by decide) (Or.inr (by decide))).trans e.passesWord
  · exact (done.frame_word h.initializing.space 112 (by decide) (Or.inr (by decide))).trans e.variantWord
  · exact (done.frame_word h.initializing.space 184 (by decide) (Or.inr (by decide))).trans e.lanesWord

theorem initialized_output {s t : State} {p : Params} (h : VG.Proof.Argon2.X86_64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  refine ⟨h.output.positive, h.output.bound, ?_,
    (done.frame_word h.initializing.space 264 (by decide) (Or.inr (by decide))).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.bp]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem initialized_setup {s t : State} {p : Params} (h : VG.Proof.Argon2.X86_64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Ready p t := by
  have params := h.environment.parameters
  have product : p.laneLen ≤ p.lanes * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ p.lanes from params.lanesPositive)
  refine ⟨VG.Proof.Argon2.X86_64.InitFill.initialized_environment h done, ?_, done.stride⟩
  have bound := h.initializing.space.bound
  have bytes := Nat.mul_le_mul_left 1024 product
  omega

theorem initialized_represents {s t : State} {p : Params} (h : VG.Proof.Argon2.X86_64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
      (initMemory p (Spec.Blake2.bytesAt s.mem (s.gpr .rbp) 64)).memory := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  rw [base]
  have segments := Proof.Argon2.laneLen_segments p h.environment.parameters.lanesPositive
  have minimum := h.environment.parameters.segment_bound.1
  exact done.initialized.represents h.environment.parameters.lanesPositive (by omega)

end VG.Proof.Argon2.X86_64.InitFill
end

/-! Merged from `Proof.Argon2.X86_64.InitFillFrames`. -/
section
/-! Each stage writes only the matrix, hash scratch, output, call stack and local hash prefix. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨FinalOutput.work s, 16384⟩,
    ⟨FinalOutput.output s, p.tagLen⟩, below (s.gpr .rsp) 24, ⟨s.gpr .rbp, 72⟩]

theorem initialization_frame {s t : State} {p : Params} (h : VG.Proof.Argon2.X86_64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : Frame (VG.Proof.Argon2.X86_64.InitFill.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have blocks := Proof.Argon2.blocks_lanes p h.environment.parameters.lanesPositive
    exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], by rw [blocks, Nat.mul_comm 1024]; intro _ h; exact h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], by rw [h.scratch]; intro _ h; exact h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], Offset.sub_base _ (by decide)⟩

theorem setup_frame {s t : State} {p : Params} (h : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem) :
    Frame (VG.Proof.Argon2.X86_64.InitFill.writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .rbp, 72⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], Region.sub_prefix (by decide)⟩

theorem filling_frame {s t : State} {p : Params} (positive : 0 < p.blocks) (h : Frame (FillFinish.writes s p) s.mem t.mem) :
    Frame (VG.Proof.Argon2.X86_64.InitFill.writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillFinish.writes, FillIterations.writes, Finish.writes,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], fun _ h => h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.gpr .rsp) 24, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], Region.sub_prefix (by omega)⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.InitFill.writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.InitFill
end

/-! Exact initialization, every filling pass, final reduction and H′ after the reviewed H₀. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def result (p : Params) (h0 : List Byte) : List Byte :=
  Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes (initMemory p h0)).memory

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = VG.Proof.Argon2.X86_64.InitFill.result p (bytesAt s.mem (s.gpr .rbp) 64)
  bp : t.gpr .rbp = s.gpr .rbp
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.InitFill.writes s p) s.mem t.mem

theorem writes_eq (s t : State) (p : Params) (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
    (base : FillKernel.matrix t = FillKernel.matrix s) (work : FinalOutput.work t = FinalOutput.work s)
    (output : FinalOutput.output t = FinalOutput.output s) : VG.Proof.Argon2.X86_64.InitFill.writes t p = VG.Proof.Argon2.X86_64.InitFill.writes s p := by
  unfold VG.Proof.Argon2.X86_64.InitFill.writes
  rw [bp, sp, base, work, output]

theorem code_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params) (h : VG.Proof.Argon2.X86_64.InitFill.Ready p s) :
    WP isa (Impl.Argon2.X86_64.InitFill.code name (HPrime.hash v)) s (VG.Proof.Argon2.X86_64.InitFill.Done s · p) := by
  have params := h.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have blocks := Proof.Argon2.lastIndex_bounds p params.lanesPositive params.segment_bound.1 0 params.lanesPositive
  unfold Impl.Argon2.X86_64.InitFill.code
  refine WP.seq ((MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen h.initializing
    params.lanesPositive (Nat.lt_trans params.lanesBound (by decide)) q).mono ?_)
  intro a initialized
  have setupReady := VG.Proof.Argon2.X86_64.InitFill.initialized_setup h initialized
  have initializedBase : FillKernel.matrix a = FillKernel.matrix s :=
    initialized.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have initializedWork : FinalOutput.work a = FinalOutput.work s :=
    initialized.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have initializedOutput : FinalOutput.output a = FinalOutput.output s :=
    initialized.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have rep : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks
      (initMemory p (bytesAt s.mem (s.gpr .rbp) 64)).memory := by
    rw [initializedBase]
    exact initialized.initialized.represents params.lanesPositive (by omega)
  refine WP.seq ((FillSetup.code_ok a p setupReady).mono ?_)
  intro b prepared
  refine (FillFinish.code_ok v name b p (prepared.finish_ready setupReady (VG.Proof.Argon2.X86_64.InitFill.initialized_output h initialized) h.positive)
    (initMemory p (bytesAt s.mem (s.gpr .rbp) 64)) (prepared.represents setupReady _ rep)).mono ?_
  intro t filled
  have bp := prepared.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have sp := prepared.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have work : FinalOutput.work b = FinalOutput.work a := prepared.words 248 (by decide) (by decide)
  have output : FinalOutput.output b = FinalOutput.output a := prepared.words 256 (by decide) (by decide)
  refine ⟨?_, (filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans (bp.trans initialized.bp),
    (filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans (sp.trans initialized.sp),
    filled.rd.trans (prepared.rd.trans initialized.rd), filled.wr.trans (prepared.wr.trans initialized.wr), ?_⟩
  · have digest := filled.digest
    rw [output, initializedOutput] at digest
    exact digest
  · have initialFrame := VG.Proof.Argon2.X86_64.InitFill.initialization_frame h initialized
    have setupFrame := VG.Proof.Argon2.X86_64.InitFill.setup_frame (p := p) prepared.frame
    rw [VG.Proof.Argon2.X86_64.InitFill.writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at setupFrame
    have fillFrame := VG.Proof.Argon2.X86_64.InitFill.filling_frame (by omega : 0 < p.blocks) filled.frame
    rw [VG.Proof.Argon2.X86_64.InitFill.writes_eq a b p bp sp prepared.matrix work output,
      VG.Proof.Argon2.X86_64.InitFill.writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at fillFrame
    exact (initialFrame.trans setupFrame).trans fillFrame

theorem result_derive (p : Params) (password salt secret ad : List Byte) :
    VG.Proof.Argon2.X86_64.InitFill.result p (initialHash p password salt secret ad) = derive p password salt secret ad := by
  unfold VG.Proof.Argon2.X86_64.InitFill.result derive
  rw [Proof.Argon2.iterations_fill]

end VG.Proof.Argon2.X86_64.InitFill

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupCT`. -/
section

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupTrace`. -/
section
/-! Cache reset and initial-index selection branch only on public parameters. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure RelatedReady (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s
  right : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem RelatedReady.of_keeps {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {s t a b : State}
    (h : VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice s t)
    (ka : Divide.Keeps [.rax, .rcx, .r15] s a) (kb : Divide.Keeps [.rax, .rcx, .r15] t b) :
    VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice a b := by
  have protectedRegs : ∀ r ∈ [Reg.rbp, .rsp, .rbx, .r12, .r13, .r14], r ∉ [Reg.rax, .rcx, .r15] := by decide
  refine ⟨h.left.of_state (fun r hr => ka.regs r (protectedRegs r hr)) ka.mem ka.rd ka.wr,
    h.right.of_state (fun r hr => kb.regs r (protectedRegs r hr)) kb.mem kb.rd kb.wr, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .rbp (by decide), kb.regs .rbp (by decide)]; exact h.bases
  · rw [ka.regs .rsp (by decide), kb.regs .rsp (by decide)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.work

theorem reset_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) VG.Impl.Argon2.X86_64.SegmentSetup.reset (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem reset_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice) VG.Impl.Argon2.X86_64.SegmentSetup.reset (VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice) := by
  have trace := reset_trace.mono (P' := VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.SegmentSetup.reset_ok s p pass lane slice h.left, VG.Proof.Argon2.X86_64.SegmentSetup.reset_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.ready, hb.ready, ?_, ?_, ha.matrix.trans (hp.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩
  · rw [ha.regs .rbp (by simp [calleeSaved]), hb.regs .rbp (by simp [calleeSaved])]; exact hp.bases
  · rw [ha.regs .rsp (by simp [calleeSaved]), hb.regs .rsp (by simp [calleeSaved])]; exact hp.stacks

theorem first_spec_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (h : VG.Proof.Argon2.X86_64.SegmentSetup.Ready p pass lane slice s) :
    WP isa (.block first) s fun t => t.zf = decide (pass = 0 ∧ slice = 0) ∧ Divide.Keeps [.rcx] s t := by
  obtain ⟨old, words⟩ := h.words
  refine (VG.Proof.Argon2.X86_64.SegmentSetup.first_ok s (h.reads 0 (by simp))).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, words.passWord, words.sliceWord]
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 :=
    ReferenceMap.word_zero pass (Nat.lt_trans h.parameters.passBound (by decide))
  have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 :=
    ReferenceMap.word_zero slice (Nat.lt_trans h.parameters.sliceBound (by decide))
  simp only [passZero, sliceZero]

theorem first_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) (.block first) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem first_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice) (.block first)
      (fun s t => VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice s t ∧ s.zf = t.zf) := by
  have trace := first_trace.mono (P' := VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.SegmentSetup.first_spec_ok s p pass lane slice h.left, VG.Proof.Argon2.X86_64.SegmentSetup.first_spec_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps (ka.mono (by decide)) (kb.mono (by decide)), fa.trans fb.symm⟩

theorem index_trace (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice) index (fun _ _ => True) := by
  have two : RelCT isa (fun _ _ : State => True) (.block [.mov .r15 (.imm 2)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have zero : RelCT isa (fun _ _ : State => True) (.block [.mov .r15 (.imm 0)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have branches : RelCT isa (fun s t => VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice s t ∧ s.zf = t.zf)
      (.ite .e (.block [.mov .r15 (.imm 2)]) (.block [.mov .r15 (.imm 0)])) (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, h.2])
      (two.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h))
  exact (VG.Proof.Argon2.X86_64.SegmentSetup.first_public_rel p pass lane slice).seq branches

theorem prepare_trace (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice) VG.Impl.Argon2.X86_64.SegmentSetup.prepare (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.SegmentSetup.reset_public_rel p pass lane slice).seq (VG.Proof.Argon2.X86_64.SegmentSetup.index_trace p pass lane slice)

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceStartLit`. -/
section
/-! A checked literal for the chronological reference-window start. -/

namespace VG

materialize_code Impl.Argon2.X86_64.ReferenceStart.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceStartCT`. -/
section
/-! The public pass, slice and segment length determine the window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceStart

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceStart

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r) VG.Impl.Argon2.X86_64.ReferenceStart.code
    (fun s t => s.gpr .r10 = t.gpr .r10) := by
  have h : RelCT isa
      (fun s t => ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r) VG.Impl.Argon2.X86_64.ReferenceStart.code
      (fun s t => ∀ r ∈ [Reg.r10], s.gpr r = t.gpr r) :=
    RelCT.taintRegs (τ := Taint.ofRegs [.r9, .r14, .r13])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.r10] (by taint_decide)
  exact h.mono (fun _ _ h => h) (fun _ _ h => h .r10 (by simp))

end VG.Proof.Argon2.X86_64.ReferenceStart
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapWindowCT`. -/
section
/-! The chronological window branches only on the public pass and slice. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

def PublicPosition (s t : State) : Prop :=
  ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r

theorem window_rel : RelCT isa VG.Proof.Argon2.X86_64.ReferenceMap.PublicPosition window (fun _ _ => True) := by
  have start := ReferenceStart.code_rel.wpDep (fun s t _ =>
    ⟨ReferenceStart.code_ok s, ReferenceStart.code_ok t⟩)
  refine start.seq (ReferenceCount.code_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact (ha.2.regs .r9 (by decide)).trans
    ((hp .r9 (by simp)).trans (hb.2.regs .r9 (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapLaneCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FirstLaneLit`. -/
section
/-! A checked literal for the public first-slice lane override. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FirstLane.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.FirstLaneCT`. -/
section
/-! The first-slice override branches only on the public position. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem code_rel : RelCT isa
    (fun s t => s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r14 = t.gpr .r14) VG.Impl.Argon2.X86_64.FirstLane.code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9, .r14])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) (by taint_decide)

end VG.Proof.Argon2.X86_64.FirstLane
end

/-! Recover the public pass from the frame without exposing the secret word. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

def Related (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s ∧ VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index t ∧ s.gpr .rbp = t.gpr .rbp

theorem division_keeps (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceLane.code s fun t =>
      VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t := by
  refine (ReferenceLane.code_ok s
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesPositive)
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesBound)).mono ?_
  rintro t ⟨_, _, keeps⟩
  have k : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .rsi (by decide)), k⟩

theorem division_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index)
      VG.Impl.Argon2.X86_64.ReferenceLane.code (VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index) := by
  have full := (ReferenceLane.code_secret_rel.mono
    (P' := VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index) (fun _ _ _ => trivial)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨VG.Proof.Argon2.X86_64.ReferenceMap.division_keeps s p pass lane slice index hp.1,
        VG.Proof.Argon2.X86_64.ReferenceMap.division_keeps t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .rbp (by decide)).trans
    (hp.2.2.trans (hb.2.regs .rbp (by decide)).symm)⟩

theorem loadPass_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block loadPass) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

def Loaded (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index s t ∧
    s.gpr .r9 = BitVec.ofNat 64 pass ∧ t.gpr .r9 = BitVec.ofNat 64 pass

theorem loadPass_public (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) : WP isa (.block loadPass) s fun t =>
      VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index t ∧ t.gpr .r9 = BitVec.ofNat 64 pass ∧
        Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t := by
  refine (loadPass_ok s ready.passRead).mono ?_
  rintro t ⟨loaded, keeps⟩
  have k : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .rsi (by decide)), loaded.trans ready.passWord, k⟩

theorem loadPass_public_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index) (.block loadPass)
      (VG.Proof.Argon2.X86_64.ReferenceMap.Loaded p pass lane slice index) := by
  have full := (loadPass_rel.mono (P' := VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨VG.Proof.Argon2.X86_64.ReferenceMap.loadPass_public s p pass lane slice index hp.1,
        VG.Proof.Argon2.X86_64.ReferenceMap.loadPass_public t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨⟨ha.1, hb.1, (ha.2.2.regs .rbp (by decide)).trans
    (hp.2.2.trans (hb.2.2.regs .rbp (by decide)).symm)⟩, ha.2.1, hb.2.1⟩

theorem firstLane_loaded_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReferenceMap.Loaded p pass lane slice index) VG.Impl.Argon2.X86_64.FirstLane.code
      (VG.Proof.Argon2.X86_64.ReferenceMap.Loaded p pass lane slice index) := by
  have trace := FirstLane.code_rel.mono (P' := VG.Proof.Argon2.X86_64.ReferenceMap.Loaded p pass lane slice index)
    (fun _ _ hp => ⟨hp.2.1.trans hp.2.2.symm,
      hp.1.1.position.slice.trans hp.1.2.1.position.slice.symm⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t _ => ⟨FirstLane.code_ok s, FirstLane.code_ok t⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  have ka : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s a := ha.2.mono (by decide)
  have kb : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed t b := hb.2.mono (by decide)
  refine ⟨⟨hp.1.1.of_keeps ka (ha.2.regs .rsi (by decide)),
    hp.1.2.1.of_keeps kb (hb.2.regs .rsi (by decide)),
    (ka.regs .rbp (by decide)).trans (hp.1.2.2.trans (kb.regs .rbp (by decide)).symm)⟩, ?_, ?_⟩
  · exact (ha.2.regs .r9 (by decide)).trans hp.2.1
  · exact (hb.2.regs .r9 (by decide)).trans hp.2.2

theorem laneArgs_secret_rel : RelCT isa (fun _ _ => True) (.block laneArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem prepareLanes_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index) prepareLanes VG.Proof.Argon2.X86_64.ReferenceMap.PublicPosition := by
  have head := (VG.Proof.Argon2.X86_64.ReferenceMap.division_rel p pass lane slice index).seq
    ((VG.Proof.Argon2.X86_64.ReferenceMap.loadPass_public_rel p pass lane slice index).seq (VG.Proof.Argon2.X86_64.ReferenceMap.firstLane_loaded_rel p pass lane slice index))
  have trace := head.seq (laneArgs_secret_rel.mono (fun _ _ _ => trivial) (fun _ _ h => h))
  have full := trace.wpDep (fun s t hp =>
    ⟨prepareLanes_ok s p pass lane slice index hp.1,
      prepareLanes_ok t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, _, _, _, ha, hb⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact ha.pass.trans hb.pass.symm
  · exact ha.position.slice.trans hb.position.slice.symm
  · exact ha.position.segmentLength.trans hb.position.segmentLength.symm

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapCT`. -/
section
/-! Complete reference mapping has no secret-dependent execution trace. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeArgs_secret_rel :
    RelCT isa (fun _ _ => True) (.block relativeArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem wrapArgs_secret_rel :
    RelCT isa (fun _ _ => True) (.block wrapArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem tail_secret_rel :
    RelCT isa (fun _ _ => True) (.seq relative VG.Impl.Argon2.X86_64.ReferenceMap.finish) (fun _ _ => True) :=
  (relativeArgs_secret_rel.seq Relative.code_secret_rel).seq
    (wrapArgs_secret_rel.seq Wrap.code_secret_rel)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.ReferenceMap.Related p pass lane slice index) VG.Impl.Argon2.X86_64.ReferenceMap.code (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.ReferenceMap.prepareLanes_rel p pass lane slice index).seq (window_rel.seq VG.Proof.Argon2.X86_64.ReferenceMap.tail_secret_rel)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.RandomSourceCounter`. -/
section
/-! The stored address counter remains public after either source. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

def counterValue (p : VG.Spec.Argon2.Params) (pass slice index old : Nat) : Addr :=
  BitVec.ofNat 64 (if independent p pass slice then index / 128 + 1 else old)

theorem counter_ok [CompressImpl] (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) :
    WP isa Impl.Argon2.X86_64.RandomSource.code s fun t =>
      t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) 8) 64 = VG.Proof.Argon2.X86_64.RandomSource.counterValue p pass slice index old := by
  unfold Impl.Argon2.X86_64.RandomSource.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.RandomSource.prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  refine WP.ite (!independent p pass slice) (by simp only [eval, flag]) ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by cases eq : independent p pass slice <;> simp_all
    refine (DependentWord.code_ok a p pass lane slice index next.filling).mono ?_
    rintro t ⟨_, saved⟩
    unfold VG.Proof.Argon2.X86_64.RandomSource.counterValue
    simp only [dependent]
    rw [saved.mem, saved.regs .rbp (by decide)]
    exact next.cache.words.counterWord
  · intro mode
    have independent : independent p pass slice = true := by cases eq : independent p pass slice <;> simp_all
    refine (AddressCache.code_ok p pass lane slice old a next.cache.ready).mono ?_
    intro t done
    unfold VG.Proof.Argon2.X86_64.RandomSource.counterValue
    simp only [independent, ite_true]
    rw [done.selected.counterWord, AddressCache.counter_nat, next.index_nat]

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillCompressCallCT`. -/
section
/-! Compression calls reveal only their argument addresses and stack pointer. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64

theorem call_rel [CompressImpl] {P : State → State → Prop}
    (pre : ∀ s t, P s t → VG.Proof.Argon2.X86_64.FillCompress.CallReady s ∧ VG.Proof.Argon2.X86_64.FillCompress.CallReady t ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
      s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call Impl.Argon2.X86_64.Compressor.name Impl.Argon2.X86_64.Compressor.code)
      (fun _ _ => True) := by
  apply RelCT.callEx (k := compressLocal) CompressImpl.correct CompressImpl.ct
  intro s t hp
  obtain ⟨hs, ht, di, si, dx, cx, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := VG.Proof.Argon2.X86_64.FillCompress.call_hyps s hs
  obtain ⟨pt, ct, wt⟩ := VG.Proof.Argon2.X86_64.FillCompress.call_hyps t ht
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
  exact ⟨di, si, dx, cx⟩

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Merged from `Proof.Argon2.X86_64.RandomSourceCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DependentWordLit`. -/
section
/-! Checked literal of the public predecessor-address computation. -/

namespace VG

materialize_code Impl.Argon2.X86_64.DependentWord.pointer

end VG
end

/-! Merged from `Proof.Argon2.X86_64.DependentWordCT`. -/
section
/-! The previous cell is read at an address determined by public parameters. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

structure Related (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : FillKernel.Ready p pass lane slice index s
  right : FillKernel.Ready p pass lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : FillKernel.matrix s = FillKernel.matrix t

theorem pointer_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r)
    pointer (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r12, .r13, .r14, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem read_rel : RelCT isa (fun s t => s.gpr .rax = t.gpr .rax) (.block Impl.Argon2.X86_64.DependentWord.read) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rax])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem code_rel (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.DependentWord.Related p pass lane slice index) VG.Impl.Argon2.X86_64.DependentWord.code (fun _ _ => True) := by
  have trace := pointer_rel.mono (P' := VG.Proof.Argon2.X86_64.DependentWord.Related p pass lane slice index) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.bases
    · exact h.left.position.laneLength.trans h.right.position.laneLength.symm
    · exact h.left.position.segmentLength.trans h.right.position.segmentLength.symm
    · exact h.left.position.slice.trans h.right.position.slice.symm
    · exact h.left.position.index.trans h.right.position.index.symm) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨pointer_ok s p pass lane slice index h.left, pointer_ok t p pass lane slice index h.right⟩)
  have publicTrace : RelCT isa (VG.Proof.Argon2.X86_64.DependentWord.Related p pass lane slice index) pointer
      (fun s t => s.gpr .rax = t.gpr .rax) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ⟨pa, _⟩, ⟨pb, _⟩⟩ := h
    have equal : FillKernel.previous s p lane slice index = FillKernel.previous t p lane slice index := by
      unfold FillKernel.previous; rw [hp.matrices]
    exact pa.trans (equal.trans pb.symm))
  exact publicTrace.seq VG.Proof.Argon2.X86_64.DependentWord.read_rel

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Merged from `Proof.Argon2.X86_64.AddressModeLit`. -/
section
/-! Checked literal of the segment addressing-mode computation. -/

namespace VG

materialize_code Impl.Argon2.X86_64.AddressMode.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.AddressModeCT`. -/
section
/-! Mode selection has a fixed trace at the public frame base. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) VG.Impl.Argon2.X86_64.AddressMode.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.AddressMode
end

/-! Merged from `Proof.Argon2.X86_64.AddressInputCT`. -/
section
/-! Clearing and header preparation visit fixed offsets of public pointers. -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64

theorem ClearBlock.code_rel : RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi)
    Impl.Argon2.X86_64.ClearBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem AddressHeader.code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rbp], s.gpr r = t.gpr r)
    Impl.Argon2.X86_64.AddressHeader.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbp])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64
end

/-! Merged from `Proof.Argon2.X86_64.AddressGenerationCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCallsCT`. -/
section
/-! The two address-generation compression calls have public fixed addresses. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

structure Related (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.AddressCalls.Ready s
  right : VG.Proof.Argon2.X86_64.AddressCalls.Ready t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  work : VG.Proof.Argon2.X86_64.AddressCalls.work s = VG.Proof.Argon2.X86_64.AddressCalls.work t

structure CallRelated (s t : State) : Prop where
  left : FillCompress.CallReady s
  right : FillCompress.CallReady t
  args : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = t.gpr r

theorem first_args_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (VG.Impl.Argon2.X86_64.AddressCalls.args 7168 5120 4096)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem second_args_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (VG.Impl.Argon2.X86_64.AddressCalls.args 7168 4096 6144)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem args_public_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (VG.Impl.Argon2.X86_64.AddressCalls.args x y out)) (fun _ _ => True)) :
    RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.Related (.block (VG.Impl.Argon2.X86_64.AddressCalls.args x y out)) VG.Proof.Argon2.X86_64.AddressCalls.CallRelated := by
  have trace := argTrace.mono (P' := VG.Proof.Argon2.X86_64.AddressCalls.Related) (fun _ _ hp => hp.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨args_nat_ok s hp.left x y out (by omega) (by omega) (by omega),
      args_nat_ok t hp.right x y out (by omega) (by omega) (by omega)⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨args_call_ready s a hp.left x y out hx hy ho bx by_ bo ha,
    args_call_ready t b hp.right x y out hx hy ho bx by_ bo hb, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((congrArg (fun p => VG.Proof.Argon2.X86_64.off p x) hp.work).trans hb.left.symm)
  · exact ha.right.trans ((congrArg (fun p => VG.Proof.Argon2.X86_64.off p y) hp.work).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (fun p => VG.Proof.Argon2.X86_64.off p out) hp.work).trans hb.output.symm)
  · exact ha.scratch.trans (hp.work.trans hb.scratch.symm)
  · exact (ha.keeps.regs .rsp (by decide)).trans
      (hp.stacks.trans (hb.keeps.regs .rsp (by decide)).symm)

theorem stage_rel [CompressImpl] (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (VG.Impl.Argon2.X86_64.AddressCalls.args x y out)) (fun _ _ => True)) :
    RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.Related (stage x y out) VG.Proof.Argon2.X86_64.AddressCalls.Related := by
  have call := FillCompress.call_rel (P := VG.Proof.Argon2.X86_64.AddressCalls.CallRelated)
    (fun _ _ hp => ⟨hp.left, hp.right, hp.args .rdi (by simp), hp.args .rsi (by simp),
      hp.args .rdx (by simp), hp.args .rcx (by simp), hp.args .rsp (by simp)⟩)
  have trace := (VG.Proof.Argon2.X86_64.AddressCalls.args_public_rel x y out hx hy ho bx by_ bo argTrace).seq call
  have full := trace.wpDep (fun s t hp =>
    ⟨(stage_ok s hp.left x y out hx hy ho bx by_ bo).mono fun _ h => h.1,
      (stage_ok t hp.right x y out hx hy ho bx by_ bo).mono fun _ h => h.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready, hb.ready,
    (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩

theorem calls_rel [CompressImpl] : RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.Related calls VG.Proof.Argon2.X86_64.AddressCalls.Related :=
  (VG.Proof.Argon2.X86_64.AddressCalls.stage_rel 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) VG.Proof.Argon2.X86_64.AddressCalls.first_args_rel).seq
  (VG.Proof.Argon2.X86_64.AddressCalls.stage_rel 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) VG.Proof.Argon2.X86_64.AddressCalls.second_args_rel)

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Independent-address generation keeps its entire trace independent of secrets. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

theorem Related.of_stable {s t a b : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Related s t)
    (ha : VG.Proof.Argon2.X86_64.AddressCalls.Stable s a) (hb : VG.Proof.Argon2.X86_64.AddressCalls.Stable t b) : VG.Proof.Argon2.X86_64.AddressCalls.Related a b :=
  ⟨ha.ready, hb.ready,
    (ha.regs .rbp (by simp [calleeSaved])).trans
      (h.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans
      (h.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm),
    ha.work_eq.trans (h.work.trans hb.work_eq.symm)⟩

theorem input_pointer_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (pointer 5120)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem zero_pointer_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (pointer 7168)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

structure PointRelated (s t : State) : Prop where
  related : VG.Proof.Argon2.X86_64.AddressCalls.Related s t
  pointer : s.gpr .rdi = t.gpr .rdi

theorem pointer_public_rel (offset : Nat)
    (trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (pointer offset)) (fun _ _ => True)) :
    RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.Related (.block (pointer offset)) VG.Proof.Argon2.X86_64.AddressCalls.PointRelated := by
  have publicTrace := trace.mono (P' := VG.Proof.Argon2.X86_64.AddressCalls.Related) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := publicTrace.wpDep (fun s t h =>
    ⟨pointer_ok s offset h.left.frameRead, pointer_ok t offset h.right.frameRead⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨pa, ka⟩, ⟨pb, kb⟩⟩ := h
  exact ⟨hp.of_stable (pointer_stable hp.left ka) (pointer_stable hp.right kb),
    pa.trans ((congrArg (· + displacement offset) hp.work).trans pb.symm)⟩

theorem clearAt_rel (offset : Nat) (bound : offset + 1024 ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (pointer offset)) (fun _ _ => True)) :
    RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.Related (clearAt offset) VG.Proof.Argon2.X86_64.AddressCalls.Related := by
  have clear := ClearBlock.code_rel.mono (P' := VG.Proof.Argon2.X86_64.AddressCalls.PointRelated)
    (fun _ _ h => h.pointer) (fun _ _ h => h)
  have blocks := (VG.Proof.Argon2.X86_64.AddressCalls.pointer_public_rel offset trace).seq clear
  have full := blocks.wpDep (fun s t h =>
    ⟨clearAt_ok s h.left offset bound, clearAt_ok t h.right offset bound⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.of_stable (ha.stable bound) (hb.stable bound)

structure PrepareRelated (s t : State) : Prop where
  related : VG.Proof.Argon2.X86_64.AddressCalls.Related s t
  leftReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 8
  rightReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) d) 8

theorem prepare_rel : RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.PrepareRelated VG.Impl.Argon2.X86_64.AddressCalls.prepare VG.Proof.Argon2.X86_64.AddressCalls.Related := by
  have header := AddressHeader.code_rel.mono (P' := VG.Proof.Argon2.X86_64.AddressCalls.PointRelated) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.related.bases) (fun _ _ h => h)
  have trace := (VG.Proof.Argon2.X86_64.AddressCalls.clearAt_rel 5120 (by decide) VG.Proof.Argon2.X86_64.AddressCalls.input_pointer_rel).seq
    ((VG.Proof.Argon2.X86_64.AddressCalls.clearAt_rel 7168 (by decide) VG.Proof.Argon2.X86_64.AddressCalls.zero_pointer_rel).seq
      ((VG.Proof.Argon2.X86_64.AddressCalls.pointer_public_rel 5120 VG.Proof.Argon2.X86_64.AddressCalls.input_pointer_rel).seq header))
  have narrowed := trace.mono (P' := VG.Proof.Argon2.X86_64.AddressCalls.PrepareRelated) (fun _ _ h => h.related) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_layout_ok s h.related.left h.leftReads,
      prepare_layout_ok t h.related.right h.rightReads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.related.of_stable ha.stable hb.stable

theorem code_rel [CompressImpl] : RelCT isa VG.Proof.Argon2.X86_64.AddressCalls.PrepareRelated VG.Impl.Argon2.X86_64.AddressCalls.code VG.Proof.Argon2.X86_64.AddressCalls.Related := prepare_rel.seq VG.Proof.Argon2.X86_64.AddressCalls.calls_rel

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheWordCT`. -/
section
/-! The cached random word is secret; its read address is public. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

structure WordRelated (s t : State) : Prop where
  layout : AddressCalls.Related s t
  indices : s.gpr .r15 = t.gpr .r15

theorem wordArgs_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r15], s.gpr r = t.gpr r)
    (.block wordArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem wordRead_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rcx, .rax], s.gpr r = t.gpr r)
    (.block wordRead) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rcx, .rax])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem word_rel : RelCT isa VG.Proof.Argon2.X86_64.AddressCache.WordRelated Impl.Argon2.X86_64.AddressCache.word (fun _ _ => True) := by
  have trace := wordArgs_rel.mono (P' := VG.Proof.Argon2.X86_64.AddressCache.WordRelated) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.layout.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨wordArgs_ok s h.layout.left.frameRead, wordArgs_ok t h.layout.right.frameRead⟩)
  have args : RelCT isa VG.Proof.Argon2.X86_64.AddressCache.WordRelated (.block wordArgs)
      (fun s t => ∀ r ∈ [Reg.rcx, .rax], s.gpr r = t.gpr r) := full.mono (fun _ _ h => h) (by
    intro a b h r hr
    obtain ⟨_, s, t, hp, ⟨sa, ia, _⟩, ⟨sb, ib, _⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sa.trans (hp.layout.work.trans sb.symm)
    · exact ia.trans ((congrArg (· &&& 127) hp.indices).trans ib.symm))
  exact args.seq VG.Proof.Argon2.X86_64.AddressCache.wordRead_rel

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheSelectCT`. -/
section
/-! Cache regeneration branches only on public counters. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

structure CacheRelated (s t : State) : Prop where
  prepare : AddressCalls.PrepareRelated s t
  indices : s.gpr .r15 = t.gpr .r15
  counters : s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8) 64 = t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) 8) 64
  leftWrite : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) 8) 8
  rightWrite : InRegions t.wr (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) 8) 8

structure CheckedRelated (s t : State) : Prop where
  related : VG.Proof.Argon2.X86_64.AddressCache.CacheRelated s t
  values : s.gpr .rax = t.gpr .rax
  flags : s.zf = t.zf

theorem check_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r15], s.gpr r = t.gpr r)
    (.block check) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem check_public_rel : RelCT isa VG.Proof.Argon2.X86_64.AddressCache.CacheRelated (.block check) VG.Proof.Argon2.X86_64.AddressCache.CheckedRelated := by
  have trace := check_rel.mono (P' := VG.Proof.Argon2.X86_64.AddressCache.CacheRelated) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.prepare.related.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.X86_64.AddressCache.check_ok s (h.prepare.leftReads 8 (by simp)), VG.Proof.Argon2.X86_64.AddressCache.check_ok t (h.prepare.rightReads 8 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨va, fa, ka⟩, ⟨vb, fb, kb⟩⟩ := h
  have sa := check_stable hp.prepare.related.left ka
  have sb := check_stable hp.prepare.related.right kb
  have index : a.gpr .r15 = b.gpr .r15 := (sa.regs .r15 (by simp [calleeSaved])).trans
    (hp.indices.trans (sb.regs .r15 (by simp [calleeSaved])).symm)
  have counters : a.mem.readW (VG.Proof.Argon2.X86_64.off (a.gpr .rbp) 8) 64 = b.mem.readW (VG.Proof.Argon2.X86_64.off (b.gpr .rbp) 8) 64 := by
    rw [ka.mem, kb.mem, sa.regs .rbp (by simp [calleeSaved]), sb.regs .rbp (by simp [calleeSaved])]
    exact hp.counters
  refine ⟨⟨⟨hp.prepare.related.of_stable sa sb, sa.reads hp.prepare.leftReads,
    sb.reads hp.prepare.rightReads⟩, index, counters, ?_, ?_⟩, ?_, ?_⟩
  · rw [ka.wr, sa.regs .rbp (by simp [calleeSaved])]; exact hp.leftWrite
  · rw [kb.wr, sb.regs .rbp (by simp [calleeSaved])]; exact hp.rightWrite
  · rw [va, vb, hp.indices]
  · rw [fa, fb, hp.indices, hp.counters]

theorem save_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block VG.Impl.Argon2.X86_64.AddressCache.save) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem save_public_rel : RelCT isa VG.Proof.Argon2.X86_64.AddressCache.CheckedRelated (.block VG.Impl.Argon2.X86_64.AddressCache.save) AddressCalls.PrepareRelated := by
  have trace := save_rel.mono (P' := VG.Proof.Argon2.X86_64.AddressCache.CheckedRelated)
    (fun _ _ h => h.related.prepare.related.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨save_ready s h.related.prepare.related.left h.related.leftWrite,
      save_ready t h.related.prepare.related.right h.related.rightWrite⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ha.work_eq.trans
    (hp.related.prepare.related.work.trans hb.work_eq.symm)⟩, ?_, ?_⟩
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.bases
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.stacks
  · rw [ha.rd, ha.wr, ha.regs]; exact hp.related.prepare.leftReads
  · rw [hb.rd, hb.wr, hb.regs]; exact hp.related.prepare.rightReads

theorem select_trace [CompressImpl] : RelCT isa VG.Proof.Argon2.X86_64.AddressCache.CacheRelated select (fun _ _ => True) := by
  have noop : RelCT isa (fun _ _ : State => True) (.block []) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have branches : RelCT isa VG.Proof.Argon2.X86_64.AddressCache.CheckedRelated
      (.ite .e (.block []) (.seq (.block VG.Impl.Argon2.X86_64.AddressCache.save) Impl.Argon2.X86_64.AddressCalls.code))
      (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, h.flags])
      (noop.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      ((save_public_rel.seq AddressCalls.code_rel).mono (fun _ _ h => h.1) (fun _ _ _ => trivial))
  exact check_public_rel.seq branches

structure ReadyRelated (p : Spec.Argon2.Params) (pass lane slice old : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s
  right : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old t
  pubs : VG.Proof.Argon2.X86_64.AddressCache.CacheRelated s t

theorem select_public_rel [CompressImpl] (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.AddressCache.ReadyRelated p pass lane slice old) select VG.Proof.Argon2.X86_64.AddressCache.WordRelated := by
  have trace := select_trace.mono (P' := VG.Proof.Argon2.X86_64.AddressCache.ReadyRelated p pass lane slice old)
    (fun _ _ h => h.pubs) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨selected_ok p pass lane slice old s h.left, selected_ok p pass lane slice old t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.layout, hb.layout, ?_, ?_, ha.work_eq.trans
    (hp.pubs.prepare.related.work.trans hb.work_eq.symm)⟩, ?_⟩
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.pubs.prepare.related.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.pubs.prepare.related.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.regs .r15 (by simp [calleeSaved])).trans
      (hp.pubs.indices.trans (hb.regs .r15 (by simp [calleeSaved])).symm)

theorem code_rel [CompressImpl] (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.AddressCache.ReadyRelated p pass lane slice old) VG.Impl.Argon2.X86_64.AddressCache.code (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.AddressCache.select_public_rel p pass lane slice old).seq VG.Proof.Argon2.X86_64.AddressCache.word_rel

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Source dispatch and cached-word selection use only public addresses and guards. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.RandomSource

structure Related (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s
  right : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem Related.of_keeps {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s t a b : State}
    (h : VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old s t)
    (ka : Divide.Keeps ReferenceMap.changed s a) (kb : Divide.Keeps ReferenceMap.changed t b) :
    VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old a b := by
  refine ⟨h.left.of_keeps ka, h.right.of_keeps kb, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .rbp (by decide), kb.regs .rbp (by decide)]; exact h.bases
  · rw [ka.regs .rsp (by decide), kb.regs .rsp (by decide)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.work

theorem test_rel : RelCT isa (fun _ _ : State => True) (.block test) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem prepare_rel (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old) VG.Impl.Argon2.X86_64.RandomSource.prepare
      (fun s t => VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old s t ∧ s.zf = t.zf) := by
  have trace := AddressMode.code_rel.seq VG.Proof.Argon2.X86_64.RandomSource.test_rel
  have narrowed := trace.mono (P' := VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.X86_64.RandomSource.prepare_ok s p pass lane slice index old h.left,
      VG.Proof.Argon2.X86_64.RandomSource.prepare_ok t p pass lane slice index old h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa.trans fb.symm⟩

theorem Related.cache {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old s t) : AddressCache.ReadyRelated p pass lane slice old s t := by
  refine ⟨h.left.cache.ready, h.right.cache.ready,
    ⟨⟨⟨h.left.cache.layout, h.right.cache.layout, h.bases, h.stacks, h.work⟩,
      h.left.cache.reads, h.right.cache.reads⟩, ?_, ?_, h.left.cache.write, h.right.cache.write⟩⟩
  · exact h.left.filling.position.index.trans h.right.filling.position.index.symm
  · exact h.left.cache.words.counterWord.trans h.right.cache.words.counterWord.symm

theorem code_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old) VG.Impl.Argon2.X86_64.RandomSource.code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => VG.Proof.Argon2.X86_64.RandomSource.Related p pass lane slice index old s t ∧ s.zf = t.zf)
      (.ite .e Impl.Argon2.X86_64.DependentWord.code Impl.Argon2.X86_64.AddressCache.code)
      (fun _ _ => True) := by
    apply RelCT.ite (by intro s t h; simp only [eval, h.2])
    · exact (DependentWord.code_rel p pass lane slice index).mono
        (fun _ _ h => ⟨h.1.1.left.filling, h.1.1.right.filling, h.1.1.bases, h.1.1.matrices⟩)
        (fun _ _ h => h)
    · exact (AddressCache.code_rel p pass lane slice old).mono
        (fun _ _ h => h.1.1.cache) (fun _ _ h => h)
  exact (VG.Proof.Argon2.X86_64.RandomSource.prepare_rel p pass lane slice index old).seq branches

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillWriteCT`. -/
section
/-! Both write paths have a public, fixed sequence of memory accesses. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillWrite

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r9, .rdi, .rsi], s.gpr r = t.gpr r) VG.Impl.Argon2.X86_64.FillWrite.code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9, .rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.FillWrite
end

/-! Merged from `Proof.Argon2.X86_64.FillSegmentCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSegmentBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPointersCT`. -/
section
/-! The pointer setup only branches on the public current column.
Reference coordinates may differ without changing its execution trace. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r8, .rbx, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r) VG.Impl.Argon2.X86_64.FillPointers.code
    (fun s t => ∀ r ∈ [Reg.r10], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.r8, .rbx, .r12, .r13, .r14, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.r10] (by taint_decide)

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelMappingCT`. -/
section
/-! Reference mapping exposes no more than the permitted reference coordinates. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s
  right : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : VG.Proof.Argon2.X86_64.FillKernel.matrix s = VG.Proof.Argon2.X86_64.FillKernel.matrix t
  scratch : VG.Proof.Argon2.X86_64.FillKernel.work s = VG.Proof.Argon2.X86_64.FillKernel.work t
  references : Spec.Argon2.reference p pass lane slice index (s.gpr .rdi) =
    Spec.Argon2.reference p pass lane slice index (t.gpr .rdi)

structure PointerRelated (p : VG.Spec.Argon2.Params) (lane slice index : Nat) (s t : State) : Prop where
  left : Layout p s
  right : Layout p t
  leftPosition : ReferenceMap.Position p lane slice index s
  rightPosition : ReferenceMap.Position p lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : VG.Proof.Argon2.X86_64.FillKernel.matrix s = VG.Proof.Argon2.X86_64.FillKernel.matrix t

theorem lanes_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FillKernel.lanes) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem lanes_ready (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) :
    WP isa (.block Impl.Argon2.X86_64.FillKernel.lanes) s fun t =>
      ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps ReferenceMap.changed s t := by
  refine (load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s t := keeps.mono (by decide)
  refine ⟨⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩, k⟩
  · rw [k.rd, k.wr, k.regs .rbp (by decide)]
    simpa only [VG.Proof.Argon2.X86_64.off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using h.layout.frameRead 0 (by simp)
  · rw [k.mem, k.regs .rbp (by decide)]
    simpa only [VG.Proof.Argon2.X86_64.off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord

theorem lanes_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillKernel.Related p pass lane slice index) (.block Impl.Argon2.X86_64.FillKernel.lanes)
      (ReferenceMap.Related p pass lane slice index) := by
  have trace := lanes_rel.mono (P' := VG.Proof.Argon2.X86_64.FillKernel.Related p pass lane slice index)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.X86_64.FillKernel.lanes_ready s p pass lane slice index h.left, VG.Proof.Argon2.X86_64.FillKernel.lanes_ready t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .rbp (by decide)).trans
    (hp.bases.trans (hb.2.regs .rbp (by decide)).symm)⟩

theorem mapping_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillKernel.Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.mapping
      (VG.Proof.Argon2.X86_64.FillKernel.PointerRelated p lane slice index) := by
  have trace := (VG.Proof.Argon2.X86_64.FillKernel.lanes_public_rel p pass lane slice index).seq (ReferenceMap.code_rel p pass lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨mapping_ok s p pass lane slice index h.left, mapping_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨hp.left.layout.of_keeps ha.keeps, hp.right.layout.of_keeps hb.keeps,
    hp.left.position.of_keeps ha.keeps, hp.right.position.of_keeps hb.keeps, ?_, ?_⟩
  · exact (ha.keeps.regs .rbp (by decide)).trans (hp.bases.trans (hb.keeps.regs .rbp (by decide)).symm)
  · unfold VG.Proof.Argon2.X86_64.FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]
    exact hp.matrices

theorem matrix_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FillKernel.matrix) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem pointers_trace (p : VG.Spec.Argon2.Params) (lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillKernel.PointerRelated p lane slice index) Impl.Argon2.X86_64.FillKernel.pointers
      (fun _ _ => True) := by
  have trace := matrix_rel.mono (P' := VG.Proof.Argon2.X86_64.FillKernel.PointerRelated p lane slice index)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨load_ok s .r8 232 (h.left.frameRead 232 (by simp)),
      load_ok t .r8 232 (h.right.frameRead 232 (by simp))⟩)
  have args : RelCT isa (VG.Proof.Argon2.X86_64.FillKernel.PointerRelated p lane slice index) (.block Impl.Argon2.X86_64.FillKernel.matrix)
      (fun s t => ∀ r ∈ [Reg.r8, .rbx, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r) :=
    full.mono (fun _ _ h => h) (by
      intro a b h r hr
      obtain ⟨_, s, t, hp, ⟨va, ka⟩, ⟨vb, kb⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact va.trans (hp.matrices.trans vb.symm)
      all_goals rw [ka.regs _ (by decide), kb.regs _ (by decide)]
      · exact hp.leftPosition.current.trans hp.rightPosition.current.symm
      · exact hp.leftPosition.laneLength.trans hp.rightPosition.laneLength.symm
      · exact hp.leftPosition.segmentLength.trans hp.rightPosition.segmentLength.symm
      · exact hp.leftPosition.slice.trans hp.rightPosition.slice.symm
      · exact hp.leftPosition.index.trans hp.rightPosition.index.symm)
  exact (args.seq FillPointers.code_rel).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillCompressOperationCT`. -/
section
/-! Only the compression argument addresses, public frame words and stack
pointer determine the compression-and-write trace. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

structure Related (s t : State) : Prop where
  left : OperationReady s
  right : OperationReady t
  args : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .rbp], s.gpr r = t.gpr r
  dest : destination s = destination t
  counter : VG.Proof.Argon2.X86_64.FillCompress.pass s = VG.Proof.Argon2.X86_64.FillCompress.pass t

structure BeforeWrite (s t : State) : Prop where
  leftRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 8
  rightRead : ∀ d ∈ [0, 16, 248], InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) d) 8
  bases : s.gpr .rbp = t.gpr .rbp
  words : ∀ d ∈ [0, 16, 248],
    s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rbp) d) 64 = t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) d) 64

theorem called_public {s t a b : State} (hp : VG.Proof.Argon2.X86_64.FillCompress.Related s t)
    (ha : VG.Proof.Argon2.X86_64.FillCompress.Called s a) (hb : VG.Proof.Argon2.X86_64.FillCompress.Called t b) : VG.Proof.Argon2.X86_64.FillCompress.BeforeWrite a b := by
  have abp : a.gpr .rbp = s.gpr .rbp := ha.regs .rbp (by simp [calleeSaved])
  have bbp : b.gpr .rbp = t.gpr .rbp := hb.regs .rbp (by simp [calleeSaved])
  refine ⟨?_, ?_, abp.trans ((hp.args .rbp (by simp)).trans bbp.symm), ?_⟩
  · intro d hd
    rw [ha.rd, ha.wr, abp]; exact hp.left.frameRead d hd
  · intro d hd
    rw [hb.rd, hb.wr, bbp]; exact hp.right.frameRead d hd
  · intro d hd
    rw [abp, bbp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [VG.Proof.Argon2.X86_64.FillCompress.frame_word hp.left ha 0 (by decide), VG.Proof.Argon2.X86_64.FillCompress.frame_word hp.right hb 0 (by decide)]
      exact hp.counter
    · rw [VG.Proof.Argon2.X86_64.FillCompress.frame_word hp.left ha 16 (by decide), VG.Proof.Argon2.X86_64.FillCompress.frame_word hp.right hb 16 (by decide)]
      exact hp.dest
    · rw [VG.Proof.Argon2.X86_64.FillCompress.frame_word hp.left ha 248 (by decide), VG.Proof.Argon2.X86_64.FillCompress.frame_word hp.right hb 248 (by decide),
        hp.left.workWord, hp.right.workWord]
      exact hp.args .rcx (by simp)

theorem call_public_rel [CompressImpl] : RelCT isa VG.Proof.Argon2.X86_64.FillCompress.Related
    (.call Impl.Argon2.X86_64.Compressor.name Impl.Argon2.X86_64.Compressor.code) VG.Proof.Argon2.X86_64.FillCompress.BeforeWrite := by
  have trace := VG.Proof.Argon2.X86_64.FillCompress.call_rel (P := VG.Proof.Argon2.X86_64.FillCompress.Related) (fun _ _ hp =>
    ⟨hp.left.call, hp.right.call, hp.args .rdi (by simp), hp.args .rsi (by simp),
      hp.args .rdx (by simp), hp.args .rcx (by simp), hp.args .rsp (by simp)⟩)
  have full := trace.wpDep (fun s t hp =>
    ⟨(call_ok s hp.left.call).mono fun _ h => h.1, (call_ok t hp.right.call).mono fun _ h => h.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact VG.Proof.Argon2.X86_64.FillCompress.called_public hp ha hb

theorem writeArgs_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block writeArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem writeArgs_public_rel : RelCT isa VG.Proof.Argon2.X86_64.FillCompress.BeforeWrite (.block writeArgs)
    (fun s t => ∀ r ∈ [Reg.r9, .rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := writeArgs_rel.mono (P' := VG.Proof.Argon2.X86_64.FillCompress.BeforeWrite) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨writeArgs_ok s (hp.leftRead 16 (by simp)) (hp.leftRead 248 (by simp)) (hp.leftRead 0 (by simp)),
      writeArgs_ok t (hp.rightRead 16 (by simp)) (hp.rightRead 248 (by simp)) (hp.rightRead 0 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha.2.2.1.trans ((hp.words 0 (by simp)).trans hb.2.2.1.symm)
  · exact ha.1.trans ((hp.words 16 (by simp)).trans hb.1.symm)
  · exact ha.2.1.trans ((congrArg (· + (4096 : Addr)) (hp.words 248 (by simp))).trans hb.2.1.symm)

theorem operation_rel [CompressImpl] : RelCT isa VG.Proof.Argon2.X86_64.FillCompress.Related operation (fun _ _ => True) :=
  call_public_rel.seq (writeArgs_public_rel.seq FillWrite.code_rel)

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Merged from `Proof.Argon2.X86_64.FillCompressCT`. -/
section
/-! Compose the setup trace with compression and the full block write. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

structure CodeRelated (s t : State) : Prop where
  left : VG.Proof.Argon2.X86_64.FillCompress.Ready s
  right : VG.Proof.Argon2.X86_64.FillCompress.Ready t
  args : ∀ r ∈ [Reg.rdi, .rsi, .r10, .rsp, .rbp], s.gpr r = t.gpr r
  scratch : VG.Proof.Argon2.X86_64.FillCompress.work s = VG.Proof.Argon2.X86_64.FillCompress.work t
  counter : VG.Proof.Argon2.X86_64.FillCompress.pass s = VG.Proof.Argon2.X86_64.FillCompress.pass t

theorem setup_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    VG.Impl.Argon2.X86_64.FillCompress.setup (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem prepared_public {s t a b : State} (h : VG.Proof.Argon2.X86_64.FillCompress.CodeRelated s t)
    (ha : VG.Proof.Argon2.X86_64.FillCompress.Prepared s a) (hb : VG.Proof.Argon2.X86_64.FillCompress.Prepared t b) : VG.Proof.Argon2.X86_64.FillCompress.Related a b := by
  refine ⟨ha.ready, hb.ready, ?_, ha.dest.trans ((h.args .r10 (by simp)).trans hb.dest.symm),
    ha.counter.trans (h.counter.trans hb.counter.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((h.args .rdi (by simp)).trans hb.left.symm)
  · exact ha.right.trans ((h.args .rsi (by simp)).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (· + (4096 : Addr)) h.scratch).trans hb.output.symm)
  · exact ha.scratch.trans (h.scratch.trans hb.scratch.symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      ((h.args .rsp (by simp)).trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      ((h.args .rbp (by simp)).trans (hb.regs .rbp (by simp [calleeSaved])).symm)

theorem setup_public_rel : RelCT isa VG.Proof.Argon2.X86_64.FillCompress.CodeRelated VG.Impl.Argon2.X86_64.FillCompress.setup VG.Proof.Argon2.X86_64.FillCompress.Related := by
  have trace := setup_rel.mono (P' := VG.Proof.Argon2.X86_64.FillCompress.CodeRelated)
    (fun _ _ h => h.args .rbp (by simp)) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.FillCompress.setup_ok s h.left, VG.Proof.Argon2.X86_64.FillCompress.setup_ok t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact VG.Proof.Argon2.X86_64.FillCompress.prepared_public hp ha hb

theorem code_rel [CompressImpl] : RelCT isa VG.Proof.Argon2.X86_64.FillCompress.CodeRelated VG.Impl.Argon2.X86_64.FillCompress.code (fun _ _ => True) :=
  setup_public_rel.seq VG.Proof.Argon2.X86_64.FillCompress.operation_rel

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Equal permitted references give equal compression and block-update traces. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem prepared_public {p : VG.Spec.Argon2.Params} {pass lane slice index : Nat} {s t a b : State}
    (h : VG.Proof.Argon2.X86_64.FillKernel.Related p pass lane slice index s t)
    (ha : VG.Proof.Argon2.X86_64.FillKernel.Prepared s a p pass lane slice index) (hb : VG.Proof.Argon2.X86_64.FillKernel.Prepared t b p pass lane slice index) :
    FillCompress.CodeRelated a b := by
  have currentEq : current s p lane slice index = current t p lane slice index := by
    unfold current; rw [h.matrices]
  have previousEq : previous s p lane slice index = previous t p lane slice index := by
    unfold previous; rw [h.matrices]
  have referenceEq : referenced s p pass lane slice index = referenced t p pass lane slice index := by
    unfold referenced; rw [h.references, h.matrices]
  have workA : FillCompress.work a = VG.Proof.Argon2.X86_64.FillKernel.work s := by
    unfold FillCompress.work VG.Proof.Argon2.X86_64.FillKernel.work; rw [ha.keeps.regs .rbp (by decide), ha.keeps.mem]
  have workB : FillCompress.work b = VG.Proof.Argon2.X86_64.FillKernel.work t := by
    unfold FillCompress.work VG.Proof.Argon2.X86_64.FillKernel.work; rw [hb.keeps.regs .rbp (by decide), hb.keeps.mem]
  have passA : FillCompress.pass a = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [ha.keeps.regs .rbp (by decide), ha.keeps.mem]
    exact h.left.passWord
  have passB : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [hb.keeps.regs .rbp (by decide), hb.keeps.mem]
    exact h.right.passWord
  refine ⟨ha.ready, hb.ready, ?_, workA.trans (h.scratch.trans workB.symm), passA.trans passB.symm⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.previousPtr.trans (previousEq.trans hb.previousPtr.symm)
  · exact ha.referencePtr.trans (referenceEq.trans hb.referencePtr.symm)
  · exact ha.currentPtr.trans (currentEq.trans hb.currentPtr.symm)
  · exact (ha.keeps.regs .rsp (by decide)).trans (h.stacks.trans (hb.keeps.regs .rsp (by decide)).symm)
  · exact (ha.keeps.regs .rbp (by decide)).trans (h.bases.trans (hb.keeps.regs .rbp (by decide)).symm)

theorem prepare_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillKernel.Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.prepare
      FillCompress.CodeRelated := by
  have trace := (VG.Proof.Argon2.X86_64.FillKernel.mapping_public_rel p pass lane slice index).seq (VG.Proof.Argon2.X86_64.FillKernel.pointers_trace p lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨VG.Proof.Argon2.X86_64.FillKernel.prepare_ok s p pass lane slice index h.left, VG.Proof.Argon2.X86_64.FillKernel.prepare_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact VG.Proof.Argon2.X86_64.FillKernel.prepared_public hp ha hb

theorem code_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillKernel.Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.code
      (fun _ _ => True) := (VG.Proof.Argon2.X86_64.FillKernel.prepare_public_rel p pass lane slice index).seq FillCompress.code_rel

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Merged from `Proof.Argon2.X86_64.FillBlockCounter`. -/
section
/-! Compression preserves the public cache counter selected by the random source. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

theorem counter_run [CompressImpl] {s t : State} {trace : List Leak} {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat}
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (run : Exec isa Impl.Argon2.X86_64.FillBlock.code s trace t) :
    t.mem.readW (VG.Proof.Argon2.X86_64.off (t.gpr .rbp) 8) 64 = RandomSource.counterValue p pass slice index old := by
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

end VG.Proof.Argon2.X86_64.FillBlock
end

/-! Merged from `Proof.Argon2.X86_64.FillBlockCT`. -/
section
/-! An active filling cell leaks only its specified data-dependent reference. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  references : independent p pass slice = false →
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory)

theorem Related.of_indices {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (source : RandomSource.Related p pass lane slice index old s t)
    (leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory)
    (rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory)
    (indices : (fillBlock p pass slice lane index leftState).indices =
      (fillBlock p pass slice lane index rightState).indices) :
    VG.Proof.Argon2.X86_64.FillBlock.Related p pass lane slice index old leftState rightState s t := by
  refine ⟨source, leftMatrix, rightMatrix, ?_⟩
  intro mode
  rw [Proof.Argon2.FillStep.indices p pass lane slice index leftState source.left.filling.bounds.active,
    Proof.Argon2.FillStep.indices p pass lane slice index rightState source.right.filling.bounds.active] at indices
  simp only [mode, Bool.false_eq_true, ite_false] at indices
  exact (List.cons.inj indices).1

theorem Related.reference_eq {p : VG.Spec.Argon2.Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (h : VG.Proof.Argon2.X86_64.FillBlock.Related p pass lane slice index old leftState rightState s t) :
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory) := by
  cases mode : independent p pass slice
  · exact h.references mode
  · simp only [Proof.Argon2.FillStep.random, mode, ite_true]

theorem source_public_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillBlock.Related p pass lane slice index old leftState rightState)
      Impl.Argon2.X86_64.RandomSource.code (FillKernel.Related p pass lane slice index) := by
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
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.source.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.source.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.frame_word hp.source.left 232 (by decide) (by decide)).trans
      (hp.source.matrices.trans (hb.frame_word hp.source.right 232 (by decide) (by decide)).symm)
  · exact (ha.frame_word hp.source.left 248 (by decide) (by decide)).trans
      (hp.source.work.trans (hb.frame_word hp.source.right 248 (by decide) (by decide)).symm)
  · rw [ha.random, hb.random]; exact hp.reference_eq

theorem code_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillBlock.Related p pass lane slice index old leftState rightState)
      Impl.Argon2.X86_64.FillBlock.code (fun _ _ => True) :=
  (VG.Proof.Argon2.X86_64.FillBlock.source_public_rel p pass lane slice index old leftState rightState).seq
    (FillKernel.code_rel p pass lane slice index)

end VG.Proof.Argon2.X86_64.FillBlock
end

/-! Public counters and coordinates remain related across a segment iteration. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSegment

theorem advance_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r13, .r15], s.gpr r = t.gpr r)
    (.block VG.Impl.Argon2.X86_64.FillSegment.advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r13, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

structure NextRelated (p : VG.Spec.Argon2.Params) (pass lane slice index : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : ∃ old, RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (FillBlock.Related p pass lane slice index old leftState rightState) VG.Impl.Argon2.X86_64.FillSegment.body
      (fun s t => s.cf = t.cf ∧ (index + 1 < p.segmentLen →
        VG.Proof.Argon2.X86_64.FillSegment.NextRelated p pass lane slice (index + 1)
          (fillBlock p pass slice lane index leftState) (fillBlock p pass slice lane index rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA advanceA =>
    cases eb with
    | seq fillB advanceB =>
      obtain ⟨filledTrace, _⟩ := FillBlock.code_rel p pass lane slice index old leftState rightState
        _ _ _ _ _ _ hp fillA fillB
      obtain ⟨_, sa, runA, filledA⟩ := FillBlock.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillBlock.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain ⟨counterA, readyA⟩ := filledA.ready
      obtain ⟨counterB, readyB⟩ := filledB.ready
      obtain ⟨advancedTrace, _⟩ := VG.Proof.Argon2.X86_64.FillSegment.advance_rel _ _ _ _ _ _ (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact readyA.filling.position.segmentLength.trans readyB.filling.position.segmentLength.symm
        · exact readyA.filling.position.index.trans readyB.filling.position.index.symm) advanceA advanceB
      obtain ⟨_, a', advanceRunA, valueA, flagA, keptA⟩ := advance_nat_ok _ p pass lane slice index readyA.filling
      obtain ⟨_, b', advanceRunB, valueB, flagB, keptB⟩ := advance_nat_ok _ p pass lane slice index readyB.filling
      obtain ⟨_, rfl⟩ := Exec.det advanceA advanceRunA
      obtain ⟨_, rfl⟩ := Exec.det advanceB advanceRunB
      refine ⟨by rw [filledTrace, advancedTrace], flagA.trans flagB.symm, ?_⟩
      intro active
      have nextA := next_ready readyA keptA valueA active
      have nextB := next_ready readyB keptB valueB active
      have counterWordA := FillBlock.counter_run hp.source.left leftState hp.leftMatrix fillA
      have counterWordB := FillBlock.counter_run hp.source.right rightState hp.rightMatrix fillB
      have wordEq : BitVec.ofNat 64 counterA = BitVec.ofNat 64 counterB :=
        readyA.cache.words.counterWord.symm.trans
          (counterWordA.trans (counterWordB.symm.trans readyB.cache.words.counterWord))
      have counters := (ReferenceMap.word_eq counterA counterB readyA.cache.bound readyB.cache.bound).mp wordEq
      subst counterB
      refine ⟨⟨counterA, nextA, nextB, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [keptA.regs .rbp (by decide), keptB.regs .rbp (by decide),
          filledA.regs .rbp (by simp [calleeSaved]), filledB.regs .rbp (by simp [calleeSaved])]
        exact hp.source.bases
      · rw [keptA.regs .rsp (by decide), keptB.regs .rsp (by decide),
          filledA.regs .rsp (by simp [calleeSaved]), filledB.regs .rsp (by simp [calleeSaved])]
        exact hp.source.stacks
      · unfold FillKernel.matrix
        rw [keptA.mem, keptB.mem, keptA.regs .rbp (by decide), keptB.regs .rbp (by decide)]
        exact filledA.matrix.trans (hp.source.matrices.trans filledB.matrix.symm)
      · unfold AddressCalls.work
        rw [keptA.mem, keptB.mem, keptA.regs .rbp (by decide), keptB.regs .rbp (by decide)]
        exact filledA.work.trans (hp.source.work.trans filledB.work.symm)
      · unfold FillKernel.matrix
        rw [keptA.mem, keptA.regs .rbp (by decide)]
        exact filledA.represented
      · unfold FillKernel.matrix
        rw [keptB.mem, keptB.regs .rbp (by decide)]
        exact filledB.represented

end VG.Proof.Argon2.X86_64.FillSegment
end

/-! The segment loop exposes only the reviewed segment reference log. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : VG.Spec.Argon2.Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice index count leftState).indices =
    (Proof.Argon2.segment p pass lane slice index count rightState).indices

theorem loop_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    RelCT isa (VG.Proof.Argon2.X86_64.FillSegment.Related p pass lane slice index count old leftState rightState)
      Impl.Argon2.X86_64.FillSegment.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (index old : Nat) (leftState rightState : FillState),
    index + n = p.segmentLen ∧ 0 < n ∧ VG.Proof.Argon2.X86_64.FillSegment.Related p pass lane slice index n old leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillSegment.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, counter, ls, rs, endIndex, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have blockRelated : FillBlock.Related p pass lane slice j counter ls rs s t :=
        ⟨hp.source, hp.leftMatrix, hp.rightMatrix,
          Proof.Argon2.segment_first_reference p pass lane slice j n ls rs
            hp.source.left.filling.bounds.active hp.indices⟩
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.X86_64.FillSegment.body_rel p pass lane slice j counter ls rs _ _ _ _ _ _ blockRelated ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.X86_64.FillSegment.body_ok s p pass lane slice j counter hp.source.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.segmentLen := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨⟨nextCounter, ready⟩, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at indices
        exact ⟨n, by omega, j + 1, nextCounter, fillBlock p pass slice lane j ls,
          fillBlock p pass slice lane j rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨index, old, leftState, rightState, endIndex, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillSegment
end

/-! Complete segment setup and filling expose only the specified reference log. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Related (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : VG.Proof.Argon2.X86_64.SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState).indices =
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState).indices

structure PreparedRelated (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  left : FillContext.Ready p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0 s
  right : FillContext.Ready p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0 t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) leftState).indices =
    (Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) rightState).indices

theorem prepare_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.Related p pass lane slice leftState rightState) VG.Impl.Argon2.X86_64.SegmentSetup.prepare
      (VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState) := by
  have trace := (VG.Proof.Argon2.X86_64.SegmentSetup.prepare_trace p pass lane slice).mono
    (P' := VG.Proof.Argon2.X86_64.SegmentSetup.Related p pass lane slice leftState rightState) (fun _ _ h => h.ready) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.SegmentSetup.prepare_ok s p pass lane slice h.ready.left, VG.Proof.Argon2.X86_64.SegmentSetup.prepare_ok t p pass lane slice h.ready.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.context, hb.context, ?_, ?_, ha.matrix.trans (hp.ready.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.ready.work.trans hb.work.symm), ha.represents hp.ready.left leftState.memory hp.leftMatrix,
    hb.represents hp.ready.right rightState.memory hp.rightMatrix, ?_⟩
  · rw [ha.regs .rbp (by simp [calleeSaved]) (by decide), hb.regs .rbp (by simp [calleeSaved]) (by decide)]
    exact hp.ready.bases
  · rw [ha.regs .rsp (by simp [calleeSaved]) (by decide), hb.regs .rsp (by simp [calleeSaved]) (by decide)]
    exact hp.ready.stacks
  · have indices := hp.indices
    rw [Proof.Argon2.segment_start p pass lane slice leftState hp.ready.left.parameters.segment_bound.1,
      Proof.Argon2.segment_start p pass lane slice rightState hp.ready.right.parameters.segment_bound.1] at indices
    exact indices

theorem PreparedRelated.of_keeps {p : VG.Spec.Argon2.Params} {pass lane slice : Nat} {leftState rightState : FillState}
    {s t a b : State} (h : VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState s t)
    (ka : Divide.Keeps [] s a) (kb : Divide.Keeps [] t b) :
    VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState a b := by
  refine ⟨h.left.of_keeps (ka.mono (by decide)), h.right.of_keeps (kb.mono (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, h.indices⟩
  · rw [ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.bases
  · rw [ka.regs .rsp (by simp), kb.regs .rsp (by simp)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.work
  · unfold FillKernel.matrix; rw [ka.mem, ka.regs .rbp (by simp)]; exact h.leftMatrix
  · unfold FillKernel.matrix; rw [kb.mem, kb.regs .rbp (by simp)]; exact h.rightMatrix

theorem check_context_ok (s : State) (p : VG.Spec.Argon2.Params) (pass lane slice : Nat)
    (h : FillContext.Ready p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0 s) : WP isa (.block check) s fun t =>
      t.cf = decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen) ∧ Divide.Keeps [] s t := by
  refine (VG.Proof.Argon2.X86_64.SegmentSetup.check_ok s).mono ?_
  rintro t ⟨flag, keeps⟩
  have minimum := h.parameters.segment_bound
  refine ⟨?_, keeps⟩
  rw [flag, h.position.index, h.position.segmentLength,
    ReferenceMap.word_nat (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) (Nat.lt_of_le_of_lt (VG.Proof.Argon2.X86_64.SegmentSetup.start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem check_trace : RelCT isa (fun _ _ : State => True) (.block check) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem check_public_rel (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState) (.block check)
      (fun s t => VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState s t ∧
        s.cf = decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen) ∧ t.cf = decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen)) := by
  have trace := check_trace.mono (P' := VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.X86_64.SegmentSetup.check_context_ok s p pass lane slice h.left, VG.Proof.Argon2.X86_64.SegmentSetup.check_context_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa, fb⟩

theorem code_rel [CompressImpl] (p : VG.Spec.Argon2.Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.X86_64.SegmentSetup.Related p pass lane slice leftState rightState) VG.Impl.Argon2.X86_64.SegmentSetup.code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => VG.Proof.Argon2.X86_64.SegmentSetup.PreparedRelated p pass lane slice leftState rightState s t ∧
        s.cf = decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen) ∧ t.cf = decide (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen))
      (.ite .b Impl.Argon2.X86_64.FillSegment.loop (.block [])) (fun _ _ => True) := by
    refine RelCT.ite (by intro s t h; simp only [eval, h.2.1, h.2.2]) ?_ ?_
    · intro s t ts tt a b hp ea eb
      have active : VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice < p.segmentLen := by
        have taken := hp.2
        simp only [eval, hp.1.2.1, Option.some.injEq, decide_eq_true_eq] at taken
        exact taken
      have left := hp.1.1.left.activate active (VG.Proof.Argon2.X86_64.SegmentSetup.start_active pass slice)
      have right := hp.1.1.right.activate active (VG.Proof.Argon2.X86_64.SegmentSetup.start_active pass slice)
      have related : FillSegment.Related p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice)
          (p.segmentLen - VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0 leftState rightState s t :=
        ⟨⟨left, right, hp.1.1.bases, hp.1.1.stacks, hp.1.1.matrices, hp.1.1.work⟩,
          hp.1.1.leftMatrix, hp.1.1.rightMatrix, hp.1.1.indices⟩
      exact FillSegment.loop_rel p pass lane slice (VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) (p.segmentLen - VG.Proof.Argon2.X86_64.SegmentSetup.start pass slice) 0
        leftState rightState (by omega) (by omega) _ _ _ _ _ _ related ea eb
    · have noop : RelCT isa (fun _ _ : State => True) (.block []) (fun _ _ => True) :=
        RelCT.taint (A := taint) (Taint.ofRegs [])
          (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
      exact noop.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  exact (VG.Proof.Argon2.X86_64.SegmentSetup.prepare_public_rel p pass lane slice leftState rightState).seq
    ((VG.Proof.Argon2.X86_64.SegmentSetup.check_public_rel p pass lane slice leftState rightState).seq branches)

end VG.Proof.Argon2.X86_64.SegmentSetup

end
