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
public import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelArgs
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress

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
