import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.Initial
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Impl.Argon2.AArch64.InitialBody
import VerifiedGarbage.Impl.Argon2.AArch64.InitFill
import VerifiedGarbage.Impl.Argon2.AArch64.FillFinish
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterations
import VerifiedGarbage.Impl.Argon2.AArch64.FinalOutput
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLane
import VerifiedGarbage.Impl.Argon2.AArch64.ReducePointers
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceBlock
import VerifiedGarbage.Impl.Argon2.AArch64.FinalReduction
import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
import VerifiedGarbage.Proof.Argon2.AArch64.Compress
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLanes
import VerifiedGarbage.Impl.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Argon2.AArch64.FillSetup
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Impl.Argon2.AArch64.Parameters
import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Framework.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialLit`. -/
section

/-! A checked literal for the six-word H₀ header. -/

namespace VG

materialize_code Impl.Argon2.AArch64.Initial.headerCode

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitLit`. -/
section

/-! # Checked literals for the public dimension setup blocks -/

namespace VG

materialize_code Impl.Argon2.AArch64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.AArch64.MemoryInit.lanesSetupCode

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReducePointers`. -/
section

/-! The last-lane address calculation preserves all callee-saved registers. -/

namespace VG.Proof.Argon2.AArch64.ReducePointers

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.ReducePointers

def changed : List Reg := [.x4, .x8, .x3, .x2, .x1, .x0, .x12, .x15]

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8) :
    WP isa (.block Impl.Argon2.AArch64.ReducePointers.setup) s fun t =>
      t.gpr .x4 = s.mem.readW (off (s.gpr .x19) 232) 64 ∧
      t.gpr .x8 = s.gpr .x24 ∧ t.gpr .x3 = s.gpr .x20 - 1 ∧
      Divide.Keeps [.x4, .x8, .x3, .x12, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReducePointers.setup,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.mov,
    Impl.Argon2.AArch64.Instructions.subi, Impl.Argon2.AArch64.Instructions.sub,
    Impl.Argon2.AArch64.Instructions.imm, Impl.Argon2.AArch64.Instructions.mark,
    show 1 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, and_self,
    read, BitVec.shiftLeft_zero, show (1#16).setWidth 64 = 1#64 from rfl,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    Bool.toNat_true, sub_value, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.ReducePointers.finish) s fun t =>
    t.gpr .x1 = s.gpr .x8 ∧ t.gpr .x0 = s.gpr .x4 ∧ Divide.Keeps [.x1, .x0] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReducePointers.finish, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) (lane q : Nat) (positive : 0 < q)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8)
    (laneWord : s.gpr .x24 = BitVec.ofNat 64 lane) (lengthWord : s.gpr .x20 = BitVec.ofNat 64 q) :
    WP isa VG.Impl.Argon2.AArch64.ReducePointers.code s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 232) 64 ∧
      t.gpr .x1 = Proof.Argon2.matrixCell (s.mem.readW (off (s.gpr .x19) 232) 64) ((lane + 1) * q - 1) ∧
      Divide.Keeps VG.Proof.Argon2.AArch64.ReducePointers.changed s t := by
  unfold VG.Impl.Argon2.AArch64.ReducePointers.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReducePointers.setup_ok s read).mono ?_)
  rintro a ⟨base, lan, col, ka⟩
  have column : a.gpr .x3 = BitVec.ofNat 64 (q - 1) := by
    rw [col, lengthWord]
    exact Offset.ofNat_sub_ofNat (by omega : 1 ≤ q)
  refine WP.seq ((BlockAddress.code_nat_ok a lane (q - 1) q (lan.trans laneWord) column
    ((ka.regs .x20 (by decide)).trans lengthWord)).mono ?_)
  rintro b ⟨address, kb⟩
  refine (VG.Proof.Argon2.AArch64.ReducePointers.finish_ok b).mono ?_
  rintro t ⟨src, dest, kt⟩
  refine ⟨dest.trans ((kb.regs .x4 (by decide)).trans base), ?_, ?_⟩
  · rw [src, address, base]
    unfold Proof.Argon2.matrixCell
    have offset : lane * q + (q - 1) = (lane + 1) * q - 1 := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [offset]
  · exact (ka.mono (by simp [VG.Proof.Argon2.AArch64.ReducePointers.changed])).trans
      ((kb.mono (by simp [VG.Proof.Argon2.AArch64.ReducePointers.changed])).trans (kt.mono (by simp [VG.Proof.Argon2.AArch64.ReducePointers.changed])))

end VG.Proof.Argon2.AArch64.ReducePointers

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReduceLane`. -/
section

/-! Merged from `Proof.Argon2.AArch64.ReductionState`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceBlock`. -/
section
/-! Reuse the verified word loop with allocation-level permissions. -/

namespace VG.Proof.Argon2.AArch64.ReduceBlock

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.ReduceBlock

theorem code_ok (s : State)
    (read : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr))
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (separate : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa VG.Impl.Argon2.AArch64.ReduceBlock.code s fun t =>
      blockAt t.mem (s.gpr .x0) = xorBlock (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1)) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ FillWrite.CopyKeeps s t ∧ t.sp = s.sp := by
  let a := s.withRegions [⟨s.gpr .x1, 1024⟩] [⟨s.gpr .x0, 1024⟩]
  obtain ⟨trace, t, run, written, frame, keeps, mx⟩ :=
    FillWrite.prefix_ok true 128 (by decide) a (by simp [a]) (by simp [a]) separate
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro q n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .x1, 1024⟩, ⟨s.gpr .x0, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact read q n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := write q n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have run' := Exec.widen (rd := s.rd) (wr := s.wr) run cover write
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at run'
  refine ⟨trace, t.withRegions s.rd s.wr, run', ?_, frame, ⟨keeps.1, rfl, rfl⟩, mx⟩
  exact (written_block written).trans (Proof.Argon2.xorBlock_comm _ _)

end VG.Proof.Argon2.AArch64.ReduceBlock
end

/-! Block zero is the accumulator; every lane's last block remains unchanged. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 232) 64

structure Ready (p : Params) (s : State) : Prop where
  positive : 0 < p.lanes
  minimum : 2 ≤ p.segmentLen
  bound : p.blocks * 1024 < 2 ^ 64
  read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8
  write : Covers [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, p.blocks * 1024⟩] s.wr
  frame : (⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  length : s.gpr .x20 = BitVec.ofNat 64 p.laneLen

structure Represents (p : Params) (memory : Array Block) (acc : Block) (s : State) : Prop where
  accumulator : blockAt s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) = acc
  last : ∀ lane < p.lanes,
    blockAt s.mem (Proof.Argon2.matrixCell (VG.Proof.Argon2.AArch64.ReductionState.matrix s) (Proof.Argon2.lastIndex p lane)) =
      memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock

theorem Ready.block_cover {p : Params} {s : State} (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s) (k : Nat) (active : k < p.blocks) :
    Covers [⟨Proof.Argon2.matrixCell (VG.Proof.Argon2.AArch64.ReductionState.matrix s) k, 1024⟩] s.wr := by
  have sub : Covers [⟨Proof.Argon2.matrixCell (VG.Proof.Argon2.AArch64.ReductionState.matrix s) k, 1024⟩] [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, p.blocks * 1024⟩] :=
    Covers.of_sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, p.blocks * 1024⟩, by simp, k * 1024, rfl, by change k * 1024 + 1024 ≤ p.blocks * 1024; omega⟩)
  exact fun a n ha => h.write a n (sub a n ha)

theorem Ready.accumulator_cover {p : Params} {s : State} (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s) :
    Covers [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩] s.wr := by
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using h.block_cover 0 (by omega)

theorem Ready.of_keeps {p : Params} {s t : State} (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s)
    (k : Divide.Keeps ReducePointers.changed s t) : VG.Proof.Argon2.AArch64.ReductionState.Ready p t := by
  have bp := k.regs .x19 (by decide)
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [k.mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (k.regs .x20 (by decide)).trans h.length⟩
  · rw [k.rd, k.wr, bp]; exact h.read
  · rw [base, k.wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_keeps {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : VG.Proof.Argon2.AArch64.ReductionState.Represents p memory acc s) (k : Divide.Keeps ReducePointers.changed s t) : VG.Proof.Argon2.AArch64.ReductionState.Represents p memory acc t := by
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [k.mem, k.regs .x19 (by decide)]
  constructor
  · rw [k.mem, base]; exact h.accumulator
  · rw [k.mem, base]; exact h.last

end VG.Proof.Argon2.AArch64.ReductionState
end

/-! A lane reduction writes only the accumulator, retaining every last-lane block. -/

namespace VG.Proof.Argon2.AArch64.ReduceLane

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Done (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  ready : VG.Proof.Argon2.AArch64.ReductionState.Ready p t
  represented : ReductionState.Represents p memory acc t
  base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (lane : Nat) (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s) (active : lane < p.lanes)
    (laneWord : s.gpr .x24 = BitVec.ofNat 64 lane) (memory : Array Block) (acc : Block)
    (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.AArch64.ReduceLane.code s
      (VG.Proof.Argon2.AArch64.ReduceLane.Done s · p memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  have lastBounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
  have q : 0 < p.laneLen := by
    have eq := Proof.Argon2.laneLen_segments p h.positive
    have minimum := h.minimum
    omega
  unfold Impl.Argon2.AArch64.ReduceLane.code
  refine WP.seq ((ReducePointers.code_ok s lane p.laneLen q h.read laneWord h.length).mono ?_)
  rintro a ⟨dest, src, keeps⟩
  have ha := h.of_keeps keeps
  have rep := represented.of_keeps keeps
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix a = VG.Proof.Argon2.AArch64.ReductionState.matrix s := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have dest' : a.gpr .x0 = VG.Proof.Argon2.AArch64.ReductionState.matrix a := dest.trans base.symm
  have src' : a.gpr .x1 = Proof.Argon2.matrixCell (VG.Proof.Argon2.AArch64.ReductionState.matrix a) (Proof.Argon2.lastIndex p lane) := by rw [base]; exact src
  have sourceWrite : Covers [⟨a.gpr .x1, 1024⟩] a.wr := by rw [src']; exact ha.block_cover _ lastBounds.2
  have sourceRead : Covers [⟨a.gpr .x1, 1024⟩] (a.rd ++ a.wr) := by
    intro x n hx
    obtain ⟨r, hr, hc⟩ := sourceWrite x n hx
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have destWrite : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by rw [dest']; exact ha.accumulator_cover
  have sep : (⟨a.gpr .x1, 1024⟩ : Region).Disjoint ⟨a.gpr .x0, 1024⟩ := by
    rw [src', dest']
    simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
      Proof.Argon2.matrixCell_disjoint (VG.Proof.Argon2.AArch64.ReductionState.matrix a) p.blocks (Proof.Argon2.lastIndex p lane) 0 ha.bound
        lastBounds.2 (by omega) (by omega)
  refine (ReduceBlock.code_ok a sourceRead destWrite sep).mono ?_
  rintro t ⟨written, frame, copied, mx⟩
  rw [dest'] at frame written
  have bp : t.gpr .x19 = a.gpr .x19 := copied.1 .x19 (by decide) (by decide) (by decide) (by decide)
  have base' : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix a := by
    unfold VG.Proof.Argon2.AArch64.ReductionState.matrix
    rw [bp]
    exact frame.readW (r := ⟨a.gpr .x19, 272⟩) (Offset.contains_base _ (by decide) (by decide))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact ha.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  refine ⟨?_, ?_, base'.trans base, ?_, copied.2.1.trans keeps.rd, copied.2.2.trans keeps.wr,
    ?_, mx.trans keeps.sp⟩
  · refine ⟨ha.positive, ha.minimum, ha.bound, ?_, ?_, ?_, (copied.1 .x20 (by decide) (by decide) (by decide) (by decide)).trans ha.length⟩
    · rw [copied.2.1, copied.2.2, bp]; exact ha.read
    · rw [base', copied.2.2]; exact ha.write
    · rw [base', bp]; exact ha.frame
  · constructor
    · rw [base', written, src', rep.accumulator, rep.last lane active]
    · intro j hj
      rw [base']
      apply Eq.trans _ (rep.last j hj)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p ha.positive ha.minimum j hj
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (VG.Proof.Argon2.AArch64.ReductionState.matrix a) p.blocks (Proof.Argon2.lastIndex p j) 0 ha.bound
          bounds.2 (by omega) (by omega)
  · intro r hr
    have ne : r ≠ .x8 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have unchanged : r ∉ ReducePointers.changed := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (copied.1 r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2).trans (keeps.regs r unchanged)
  · rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.AArch64.ReduceLane

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReductionLoopState`. -/
section

/-! Public loop metadata survives accumulator writes and register-only advancement. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

theorem Ready.of_state {p : Params} {s t : State} (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s)
    (bp : t.gpr .x19 = s.gpr .x19) (length : t.gpr .x20 = s.gpr .x20)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.AArch64.ReductionState.Ready p t := by
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, length.trans h.length⟩
  · rw [rd, wr, bp]; exact h.read
  · rw [base, wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_state {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : VG.Proof.Argon2.AArch64.ReductionState.Represents p memory acc s) (bp : t.gpr .x19 = s.gpr .x19) (mem : t.mem = s.mem) :
    VG.Proof.Argon2.AArch64.ReductionState.Represents p memory acc t := by
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [mem, bp]
  constructor
  · rw [mem, base]; exact h.accumulator
  · rw [mem, base]; exact h.last

theorem frame_word {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s) (done : ReduceLane.Done s t p memory acc) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
          omega))) (by decide)

end VG.Proof.Argon2.AArch64.ReductionState

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputReady`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FinalOutputArgs`. -/
section
/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def changed : List Reg := [.x0, .x1, .x2, .x3, .x4]

structure Arguments (s t : State) : Prop where
  input : t.gpr .x0 = ReductionState.matrix s
  inputLength : t.gpr .x1 = 1024
  output : t.gpr .x2 = VG.Proof.Argon2.AArch64.FinalOutput.output s
  outputLength : t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 264) 64
  work : t.gpr .x4 = VG.Proof.Argon2.AArch64.FinalOutput.work s
  keeps : Divide.Keeps VG.Proof.Argon2.AArch64.FinalOutput.changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block Impl.Argon2.AArch64.FinalOutput.args) s (VG.Proof.Argon2.AArch64.FinalOutput.Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.FinalOutput.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 1024 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide,
    show 256 % 8 = 0 ∧ 256 < 4096 * 8 from by decide,
    show 264 % 8 = 0 ∧ 264 < 4096 * 8 from by decide,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1024#16).setWidth 64 = 1024#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · constructor
    · intro r hr
      simp only [VG.Proof.Argon2.AArch64.FinalOutput.changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem Arguments.regs {s t : State} (h : VG.Proof.Argon2.AArch64.FinalOutput.Arguments s t) (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ VG.Proof.Argon2.AArch64.FinalOutput.changed := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! Final output uses matrix block zero and the original disjoint hash scratch allocation. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  positive : 1 ≤ p.tagLen
  bound : p.tagLen < 2 ^ 32
  reads : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  tagWord : s.mem.readW (off (s.gpr .x19) 264) 64 = BitVec.ofNat 64 p.tagLen
  input : Covers [⟨ReductionState.matrix s, 1024⟩] (s.rd ++ s.wr)
  outputWrite : Covers [⟨VG.Proof.Argon2.AArch64.FinalOutput.output s, p.tagLen⟩] s.wr
  workWrite : (⟨VG.Proof.Argon2.AArch64.FinalOutput.work s, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨ReductionState.matrix s, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FinalOutput.work s, 16384⟩
  outputWork : (⟨VG.Proof.Argon2.AArch64.FinalOutput.output s, p.tagLen⟩ : Region).Disjoint ⟨VG.Proof.Argon2.AArch64.FinalOutput.work s, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨ReductionState.matrix s, 1024⟩
  stackOutput : (below s.sp 16).Disjoint ⟨VG.Proof.Argon2.AArch64.FinalOutput.output s, p.tagLen⟩
  stackWork : (below s.sp 16).Disjoint ⟨VG.Proof.Argon2.AArch64.FinalOutput.work s, 16384⟩

theorem Arguments.ready {p : Params} {s t : State} (h : VG.Proof.Argon2.AArch64.FinalOutput.Ready p s) (a : VG.Proof.Argon2.AArch64.FinalOutput.Arguments s t) :
    FinalCall.CallReady p.tagLen t := by
  have sp := a.keeps.sp
  constructor
  · rw [sp]; exact h.stackMinimum
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

end VG.Proof.Argon2.AArch64.FinalOutput

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlockLit`. -/
section

namespace VG.Impl.Argon2.AArch64.ReduceBlock

materialize_code VG.Impl.Argon2.AArch64.ReduceBlock.code

end VG.Impl.Argon2.AArch64.ReduceBlock

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FinishReady`. -/
section

/-! Merged from `Proof.Argon2.AArch64.ReduceLanesBody`. -/
section
/-! One reduction iteration advances a public lane and preserves the accumulator invariant. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (lane : Nat) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  active : lane < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  laneWord : s.gpr .x24 = BitVec.ofNat 64 lane
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Done (s t : State) (p : Params) (lane : Nat) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 (lane + 1)
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp
  cf : eval (.nonzero .x .x14) t = some (decide (lane + 1 < p.lanes))
  next : lane + 1 < p.lanes → VG.Proof.Argon2.AArch64.ReduceLanes.Ready p (lane + 1) t

theorem body_ok (s : State) (p : Params) (lane : Nat) (h : VG.Proof.Argon2.AArch64.ReduceLanes.Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.AArch64.ReduceLanes.body s
      (VG.Proof.Argon2.AArch64.ReduceLanes.Done s · p lane memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  unfold Impl.Argon2.AArch64.ReduceLanes.body Impl.Argon2.AArch64.ReduceLanes.advance
  refine WP.seq ((ReduceLane.code_ok s p lane h.allocation h.active h.laneWord memory acc represented).mono ?_)
  intro a reduced
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 184) 8 := by
    rw [reduced.rd, reduced.wr, reduced.regs .x19 (by simp [FillCompress.loopRegs])]; exact h.lanesRead
  have word := (ReductionState.frame_word h.allocation reduced 184 (by decide)).trans h.lanesWord
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [reduced.regs .x24 (by simp [FillCompress.loopRegs]), h.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.active
  have lanesBound := h.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [word, ReferenceMap.word_nat p.lanes (by omega)]; omega
  refine (FillLanes.advance_ok a read left right).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix a := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [keeps.mem, bp]
  have nextWord := value.trans added
  refine ⟨reduced.represented.of_state bp keeps.mem, base.trans reduced.base, nextWord,
    ?_, keeps.rd.trans reduced.rd, keeps.wr.trans reduced.wr, ?_, keeps.sp.trans reduced.sp, ?_, ?_⟩
  · intro r hr bx
    have outside : r ∉ [Reg.x24, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reduced.regs r hr)
  · rw [keeps.mem]; exact reduced.frame
  · rw [flag, added, word, ReferenceMap.word_nat (lane + 1) (by have bound := h.lanesBound; have active := h.active; omega),
      ReferenceMap.word_nat p.lanes (Nat.lt_trans h.lanesBound (by decide))]
  · intro active
    refine ⟨reduced.ready.of_state bp (keeps.regs .x20 (by decide)) keeps.mem keeps.rd keeps.wr,
      active, h.lanesBound, nextWord, ?_, ?_⟩
    · rw [keeps.rd, keeps.wr, bp]; exact read
    · rw [keeps.mem, bp]; exact word

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Merged from `Proof.Argon2.AArch64.ReductionInit`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReductionClear`. -/
section
/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : VG.Proof.Argon2.AArch64.ReductionState.Ready p t
  represented : VG.Proof.Argon2.AArch64.ReductionState.Represents p memory zeroBlock t
  base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem clear_ok (s : State) (p : Params) (h : VG.Proof.Argon2.AArch64.ReductionState.Ready p s)
    (dest : s.gpr .x0 = VG.Proof.Argon2.AArch64.ReductionState.matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ClearBlock.code s (VG.Proof.Argon2.AArch64.ReductionState.Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .x0, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ClearBlock.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .x19 (by decide) (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .x20 (by decide) (by decide)).trans h.length⟩
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
        Proof.Argon2.matrixCell_disjoint (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks (Proof.Argon2.lastIndex p lane) 0 h.bound
          bounds.2 (by omega) (by omega)

theorem Cleared.frame_word {p : Params} {s t : State} {memory : Array Block}
    (ready : VG.Proof.Argon2.AArch64.ReductionState.Ready p s) (done : VG.Proof.Argon2.AArch64.ReductionState.Cleared s t p memory) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.keeps.1 .x19 (by decide) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega))) (by decide)

end VG.Proof.Argon2.AArch64.ReductionState
end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanes`. -/
section
/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : VG.Proof.Argon2.AArch64.ReduceLanes.Done s t p lane memory acc) (last : lane + 1 = p.lanes) : VG.Proof.Argon2.AArch64.ReduceLanes.Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : VG.Proof.Argon2.AArch64.ReduceLanes.Done s a p lane memory acc) (rest : VG.Proof.Argon2.AArch64.ReduceLanes.Finished a t p memory result) : VG.Proof.Argon2.AArch64.ReduceLanes.Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : VG.Proof.Argon2.AArch64.ReduceLanes.Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.AArch64.ReduceLanes.loop s
      (VG.Proof.Argon2.AArch64.ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory lane count acc)) := by
  induction count generalizing s lane acc with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.AArch64.ReduceLanes.body_ok s p lane h memory acc represented
    rw [Proof.Argon2.reduction_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Establish the invariant for reducing all lanes, retaining the input matrix's last blocks. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  lanesBound : p.lanes < 2 ^ 32
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8) :
    WP isa (.block Impl.Argon2.AArch64.ReductionInit.setup) s fun t =>
      t.gpr .x0 = VG.Proof.Argon2.AArch64.ReductionState.matrix s ∧ t.gpr .x24 = 0 ∧ Divide.Keeps [.x0, .x24] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReductionInit.setup,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (0#16).setWidth 64 = 0#64 from rfl, read, RegUpd.gpr_write,
    reduceCtorEq, ite_false, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

structure Prepared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : ReduceLanes.Ready p 0 t
  represented : ReductionState.Represents p memory zeroBlock t
  base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (h : VG.Proof.Argon2.AArch64.ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ReductionInit.code s (VG.Proof.Argon2.AArch64.ReductionInit.Prepared s · p memory) := by
  unfold Impl.Argon2.AArch64.ReductionInit.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.ReductionInit.setup_ok s h.allocation.read).mono ?_)
  rintro a ⟨dest, lane, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix a = VG.Proof.Argon2.AArch64.ReductionState.matrix s := by unfold VG.Proof.Argon2.AArch64.ReductionState.matrix; rw [keeps.mem, bp]
  have ha := h.allocation.of_state bp (keeps.regs .x20 (by decide)) keeps.mem keeps.rd keeps.wr
  have rep : Proof.Argon2.Represents a.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix a) p.blocks memory := by rw [keeps.mem, base]; exact represented
  refine (ReductionState.clear_ok a p ha (dest.trans base.symm) memory rep).mono ?_
  intro t cleared
  refine ⟨⟨cleared.ready, ha.positive, h.lanesBound,
    (cleared.keeps.1 .x24 (by decide) (by decide)).trans lane, ?_, ?_⟩,
    cleared.represented, cleared.base.trans base, ?_, cleared.keeps.2.1.trans keeps.rd,
    cleared.keeps.2.2.trans keeps.wr, ?_, cleared.sp.trans keeps.sp⟩
  · rw [cleared.keeps.2.1, cleared.keeps.2.2, cleared.keeps.1 .x19 (by decide) (by decide), keeps.rd, keeps.wr, bp]
    exact h.lanesRead
  · rw [cleared.frame_word ha 184 (by decide), keeps.mem, bp]; exact h.lanesWord
  · intro r hr bx
    have ne : r ≠ .x8 ∧ r ≠ .x9 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notDest : r ≠ .x0 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (cleared.keeps.1 r ne.1 ne.2).trans (keeps.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨notDest, bx⟩))
  · have frame := cleared.frame
    rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.AArch64.ReductionInit
end

/-! Merged from `Proof.Argon2.AArch64.ReductionInitCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReducePointersCT`. -/
section
/-! Pointer preparation reads one public frame location and performs fixed arithmetic. -/

namespace VG.Proof.Argon2.AArch64.ReducePointers

open VG VG.AArch64

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ReducePointers.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.ReducePointers
end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceLanesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceLaneCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceBlockCT`. -/
section
/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceBlock

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r)
    VG.Impl.Argon2.AArch64.ReduceBlock.code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.AArch64.ReduceBlock
end

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceLane

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.ReductionState.Ready p s
  right : VG.Proof.Argon2.AArch64.ReductionState.Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .x24 = BitVec.ofNat 64 lane
  rightLane : t.gpr .x24 = BitVec.ofNat 64 lane
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : VG.Proof.Argon2.AArch64.ReductionState.matrix s = VG.Proof.Argon2.AArch64.ReductionState.matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReduceLane.Related p lane) Impl.Argon2.AArch64.ReducePointers.code
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := VG.Proof.Argon2.AArch64.ReduceLane.Related p lane) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨sp, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  refine ⟨sp, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .x19) 232) 64 = t.mem.readW (off (t.gpr .x19) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReduceLane.Related p lane) Impl.Argon2.AArch64.ReduceLane.code (fun _ _ => True) :=
  (VG.Proof.Argon2.AArch64.ReduceLane.pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.AArch64.ReduceLane
end

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.ReduceLanes.Ready p lane s
  right : VG.Proof.Argon2.AArch64.ReduceLanes.Ready p lane t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : VG.Proof.Argon2.AArch64.ReductionState.matrix s = VG.Proof.Argon2.AArch64.ReductionState.matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReduceLanes.advance) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReduceLanes.Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (lane + 1 < p.lanes → VG.Proof.Argon2.AArch64.ReduceLanes.Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.stacks, hp.matrices⟩
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
      have bases := (reducedA.regs .x19 (by simp [FillCompress.loopRegs])).trans
        (hp.bases.trans (reducedB.regs .x19 (by simp [FillCompress.loopRegs])).symm)
      have stacks := reducedA.sp.trans (hp.stacks.trans reducedB.sp.symm)
      obtain ⟨advanceTrace, _⟩ := VG.Proof.Argon2.AArch64.ReduceLanes.advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.AArch64.ReduceLanes.body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.AArch64.ReduceLanes.body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReduceLanes.Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    VG.Proof.Argon2.AArch64.ReduceLanes.Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.ReduceLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.AArch64.ReduceLanes.body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.AArch64.ReduceLanes.body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega, j + 1, _, _, by omega, by omega, next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.ReductionInit.Ready p s
  right : VG.Proof.Argon2.AArch64.ReductionInit.Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : VG.Proof.Argon2.AArch64.ReductionState.matrix s = VG.Proof.Argon2.AArch64.ReductionState.matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReductionInit.setup) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem clear_rel : RelCT isa (fun s t => s.gpr .x0 = t.gpr .x0 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ClearBlock.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (VG.Proof.Argon2.AArch64.ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.AArch64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, setupSp⟩ := VG.Proof.Argon2.AArch64.ReductionInit.setup_rel _ _ _ _ _ _ ⟨hp.bases, hp.stacks⟩ setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := VG.Proof.Argon2.AArch64.ReductionInit.setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := VG.Proof.Argon2.AArch64.ReductionInit.setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := VG.Proof.Argon2.AArch64.ReductionInit.clear_rel _ _ _ _ _ _ ⟨destA.trans (hp.matrices.trans destB.symm), setupSp⟩ clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.AArch64.ReductionInit.code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.AArch64.ReductionInit.code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReductionInit
end

/-! Merged from `Proof.Argon2.AArch64.FinalReduction`. -/
section
/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.AArch64.FinalReduction

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.AArch64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.sp.trans prepared.sp, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.AArch64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.AArch64.FinalReduction
end

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : VG.Proof.Argon2.AArch64.Finish.Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)
  have sp := done.sp
  have output : FinalOutput.output t = FinalOutput.output s := VG.Proof.Argon2.AArch64.Finish.frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := VG.Proof.Argon2.AArch64.Finish.frame_word ready.reduction done 248 (by decide)
  refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
    (VG.Proof.Argon2.AArch64.Finish.frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact ready.output.stackMinimum
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.Finish

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.FillFinish`. -/
section

/-! Merged from `Proof.Argon2.AArch64.FinishStage`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalOutput`. -/
section
/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (VG.Proof.Argon2.AArch64.FinalOutput.output s) p.tagLen = VG.Spec.Argon2.finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.AArch64.FinalOutput.output s, p.tagLen⟩, ⟨VG.Proof.Argon2.AArch64.FinalOutput.work s, 16384⟩, below s.sp 16] s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : VG.Proof.Argon2.AArch64.FinalOutput.Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.AArch64.FinalOutput.code name v.hash) s (VG.Proof.Argon2.AArch64.FinalOutput.Done s · p memory) := by
  unfold Impl.Argon2.AArch64.FinalOutput.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FinalOutput.args_ok s h.reads).mono ?_)
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
  [⟨VG.Proof.Argon2.AArch64.ReductionState.matrix s, 1024⟩, ⟨FinalOutput.output s, p.tagLen⟩,
    ⟨FinalOutput.work s, 16384⟩, below s.sp 16]

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = Spec.Argon2.finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.Finish.writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : VG.Proof.Argon2.AArch64.Finish.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks memory) :
    WP isa (Impl.Argon2.AArch64.Finish.code name v.hash) s (VG.Proof.Argon2.AArch64.Finish.Done s · p memory) := by
  unfold Impl.Argon2.AArch64.Finish.code
  refine WP.seq ((FinalReduction.code_ok s p h.reduction memory represented).mono ?_)
  intro a reduced
  refine (FinalOutput.code_ok v name a p (VG.Proof.Argon2.AArch64.Finish.output_ready h reduced) memory reduced.represented.accumulator).mono ?_
  intro t written
  have output : FinalOutput.output a = FinalOutput.output s := VG.Proof.Argon2.AArch64.Finish.frame_word h.reduction reduced 256 (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := VG.Proof.Argon2.AArch64.Finish.frame_word h.reduction reduced 248 (by decide)
  refine ⟨?_, fun r hr bx => (written.regs r hr).trans (reduced.regs r hr bx),
    written.sp.trans reduced.sp, written.rd.trans reduced.rd, written.wr.trans reduced.wr, ?_⟩
  · have digest := written.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (VG.Proof.Argon2.AArch64.Finish.writes s p) s.mem a.mem := reduced.frame.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, by simp [VG.Proof.Argon2.AArch64.Finish.writes], fun _ h => h⟩)
    have lastFrame := written.frame
    rw [output, work, reduced.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [VG.Proof.Argon2.AArch64.Finish.writes], fun _ h => h⟩

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
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix t = VG.Proof.Argon2.AArch64.ReductionState.matrix s := done.matrix
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
  frame : Frame (VG.Proof.Argon2.AArch64.FillFinish.writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : VG.Proof.Argon2.AArch64.FillFinish.Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.AArch64.FillFinish.code name v.hash) s (VG.Proof.Argon2.AArch64.FillFinish.Done s · p state) := by
  unfold Impl.Argon2.AArch64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (VG.Proof.Argon2.AArch64.FillFinish.finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : VG.Proof.Argon2.AArch64.ReductionState.matrix a = VG.Proof.Argon2.AArch64.ReductionState.matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.sp.trans filled.sp, finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (VG.Proof.Argon2.AArch64.FillFinish.writes s p) s.mem a.mem := filled.frame.sub (by
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCall`. -/
section

/-! A verified H′ call initializes one 1024-byte memory block. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)
open VG.Spec.Blake2 (bytesAt)

structure CallReady (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  input : Covers [⟨s.gpr .x0, 72⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .x2, 1024⟩] s.wr
  work : (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .x0, 72⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  outputWork : (⟨s.gpr .x2, 1024⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨s.gpr .x0, 72⟩
  stackOutput : (below s.sp 16).Disjoint ⟨s.gpr .x2, 1024⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x4, 16384⟩

structure Called (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .x2) 1024 = Spec.Argon2.hPrime 1024 (bytesAt s.mem (s.gpr .x0) 72)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩, below s.sp 16] s.mem t.mem

theorem hPrime_call_hyps (s : State) (h : VG.Proof.Argon2.AArch64.MemoryInit.CallReady s)
    (inputLength : s.gpr .x1 = 72) (outputLength : s.gpr .x3 = 1024) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .x0, 72⟩]
      [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩]) ∧
    Covers [⟨s.gpr .x0, 72⟩, ⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩] s.wr := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp,
      g _ (by decide : Reg.x0 ∉ linkRegs), g _ (by decide : Reg.x1 ∉ linkRegs),
      g _ (by decide : Reg.x2 ∉ linkRegs), g _ (by decide : Reg.x3 ∉ linkRegs),
      g _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp,
      inputLength, outputLength]
    exact ⟨rfl, rfl, by decide, by decide, by decide, h.stackMinimum,
      h.inputWork, h.outputWork, h.stackInput, h.stackOutput, h.stackWork⟩
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

theorem hPrime_depth (v : HPrime.Backend) : (VG.Impl.Argon2.AArch64.HPrime.code v.hash).aarch64Depth = 1 := by
  simp only [VG.Impl.Argon2.AArch64.HPrime.code, Impl.Argon2.AArch64.HPrime.first,
    Impl.Argon2.AArch64.HPrime.chooseLength, Impl.Argon2.AArch64.HPrime.init,
    Impl.Argon2.AArch64.HPrime.absorbFixed, Impl.Argon2.AArch64.HPrime.update,
    Impl.Argon2.AArch64.HPrime.absorbInput, Impl.Argon2.AArch64.HPrime.finishInput,
    Impl.Argon2.AArch64.HPrime.finalize, Impl.Argon2.AArch64.HPrime.finishOutput,
    Impl.Argon2.AArch64.HPrime.extendDigest, Impl.Argon2.AArch64.HPrime.emitPrefix,
    Impl.Argon2.AArch64.HPrime.copy, Impl.Argon2.AArch64.HPrime.chain,
    Impl.Argon2.AArch64.HPrime.next, Impl.Argon2.AArch64.HPrime.copyRemaining,
    Code.aarch64Depth, v.ok.initDepth, v.ok.updateDepth, v.ok.finalizeDepth]
  rfl

theorem hPrime_call_ok (v : HPrime.Backend) (name : String)
    (s : State) (h : VG.Proof.Argon2.AArch64.MemoryInit.CallReady s) (inputLength : s.gpr .x1 = 72)
    (outputLength : s.gpr .x3 = 1024) :
    WP isa (.call name (VG.Impl.Argon2.AArch64.HPrime.code v.hash)) s (VG.Proof.Argon2.AArch64.MemoryInit.Called s) := by
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.AArch64.MemoryInit.hPrime_call_hyps s h inputLength outputLength
  refine WP.callF (k := HPrime.localContract) (HPrime.code_correct v) pre cover writes ?_
    (by rw [VG.Proof.Argon2.AArch64.MemoryInit.hPrime_depth]; decide)
  intro t rd wr sp frame regs digest
  change bytesAt t.mem (s.callEntry.gpr .x2) (s.callEntry.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.callEntry.gpr .x3).toNat
      (bytesAt s.mem (s.callEntry.gpr .x0) (s.callEntry.gpr .x1).toNat) at digest
  rw [State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), inputLength, outputLength,
    show (72 : Addr).toNat = 72 from rfl,
    show (1024 : Addr).toNat = 1024 from rfl] at digest
  refine ⟨digest, ?_, sp, rd, wr, ?_⟩
  · intro r hr
    have preserved : r ∈ VG.AArch64.preserved ∧ r ≠ .x30 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact regs r preserved.1 preserved.2
  · simpa only [VG.Proof.Argon2.AArch64.MemoryInit.hPrime_depth, Nat.mul_one, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitBlock`. -/
section

/-! Merged from `Proof.Argon2.AArch64.MemoryInitArgs`. -/
section
/-! # The 72-byte H₀, column and lane input to memory initialization -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

def blockMem (m : Mem) (p : Addr) (column : Nat) (lane : Addr) : Mem :=
  (m.writeW (p + 64) (BitVec.ofNat 32 column)).writeW (p + 68) (lane.setWidth 32)

theorem blockMem_frame (m : Mem) (p : Addr) (column : Nat) (lane : Addr) :
    Frame [⟨p + 64, 8⟩] m (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane) := by
  unfold VG.Proof.Argon2.AArch64.MemoryInit.blockMem
  have first : Frame [⟨p + 64, 8⟩] m (m.writeW (p + 64) (BitVec.ofNat 32 column)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa only [BitVec.add_zero] using
        Offset.contains_base (p + 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide))
  apply first.writeW (List.mem_singleton_self _)
  have eq : p + 68 = (p + 64) + BitVec.ofNat 64 4 := by rw [BitVec.add_assoc]; rfl
  rw [eq]
  exact Offset.contains_base _ (by decide : 4 + 4 ≤ 8) (by decide)

theorem blockMem_bytes (m : Mem) (p : Addr) (column : Nat) (lane : Addr) :
    bytesAt (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane) p 72 =
      bytesAt m p 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 lane.toNat := by
  have first : bytesAt (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane) p 64 = bytesAt m p 64 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply (VG.Proof.Argon2.AArch64.MemoryInit.blockMem_frame m p column lane).bytes (R := ⟨p, 64⟩) _
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
    · intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.base_disjoint _ (by decide) (by decide)

  have columnWord : (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane).readW (p + 64) 32 = BitVec.ofNat 32 column := by
    unfold VG.Proof.Argon2.AArch64.MemoryInit.blockMem
    rw [Mem.readW_writeW_sep ?_ (by decide), Mem.readW_writeW_self32]
    exact Offset.sep p (by decide) (by decide) (by decide)
  have laneWord : (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane).readW (p + 68) 32 = lane.setWidth 32 :=
    Mem.readW_writeW_self32 _ _ _
  have words := Proof.Blake2.bytesAt_add (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane) (p + 64) 4 4
  have pos : p + 64 + BitVec.ofNat 64 4 = p + 68 := by rw [BitVec.add_assoc]; rfl
  rw [pos, ← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl),
    ← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl), columnWord, laneWord] at words
  have header := Proof.Blake2.bytesAt_add (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane) p 64 8
  change bytesAt (VG.Proof.Argon2.AArch64.MemoryInit.blockMem m p column lane) (p + 64) 8 = _ at words
  rw [show BitVec.ofNat 64 64 = (64 : Addr) from rfl, first, words, ← BitVec.ofNat_toNat 32 lane, ← List.append_assoc] at header
  exact header

structure BlockArgs (s t : State) (column : Nat) : Prop where
  input : t.gpr .x0 = s.gpr .x19
  inputLength : t.gpr .x1 = 72
  output : t.gpr .x2 = s.gpr .x22
  outputLength : t.gpr .x3 = 1024
  work : t.gpr .x4 = s.gpr .x24
  other : ∀ r, r ≠ .x8 → r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 →
    t.gpr r = s.gpr r
  mem : t.mem = VG.Proof.Argon2.AArch64.MemoryInit.blockMem s.mem (s.gpr .x19) column (s.gpr .x20)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem blockArgs_ok (s : State) (column : Nat) (columnBound : column < 65536)
    (colWrite : InRegions s.wr (s.gpr .x19 + 64) 4)
    (laneWrite : InRegions s.wr (s.gpr .x19 + 68) 4) :
    WP isa (.block (blockArgs column)) s (fun t => VG.Proof.Argon2.AArch64.MemoryInit.BlockArgs s t column) := by
  have colLiteral : InRegions s.wr (s.gpr .x19 + 64#64) 4 := colWrite
  have laneLiteral : InRegions s.wr (s.gpr .x19 + 68#64) 4 := laneWrite
  have col : (BitVec.ofNat 16 column).setWidth 64 = BitVec.ofNat 64 column :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) columnBound
  apply WP.of_runBlock
  simp only [blockArgs, Impl.Argon2.AArch64.Instructions.imm,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.store32,
    columnBound, show 72 < 65536 from by decide, show 1024 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod,
    show 0 < 4096 from by decide, BitVec.shiftLeft_zero, col,
    show (72#16).setWidth 64 = 72#64 from rfl,
    show (1024#16).setWidth 64 = 1024#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    reduceCtorEq, ite_true, ite_false, colLiteral, laneLiteral, and_self,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.add_zero,
    BitVec.setWidth_eq]
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  · intro r h1 h2 h3 h4 h5 h6
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, h6, ite_false]
  · simp only [RegUpd.mem_write, VG.Proof.Argon2.AArch64.MemoryInit.blockMem, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rfl
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Initializing a block while preserving H₀ and the public lane counters -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure BlockReady (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  input : Covers [⟨s.gpr .x19, 72⟩] s.wr
  output : Covers [⟨s.gpr .x22, 1024⟩] s.wr
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  frameWork : (⟨s.gpr .x19, 72⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  frameOutput : (⟨s.gpr .x19, 72⟩ : Region).Disjoint ⟨s.gpr .x22, 1024⟩
  outputWork : (⟨s.gpr .x22, 1024⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackFrame : (below (s.sp) 16).Disjoint ⟨s.gpr .x19, 72⟩
  stackOutput : (below (s.sp) 16).Disjoint ⟨s.gpr .x22, 1024⟩
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩

theorem BlockArgs.regs {s t : State} {column : Nat} (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockArgs s t column)
    (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have hn : r ≠ .x8 ∧ r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem BlockReady.prefix {s : State} (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s) (d : Nat)
    (bound : d + 4 ≤ 72) : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 4 := by
  exact h.input _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem BlockArgs.ready {s t : State} {column : Nat} (a : VG.Proof.Argon2.AArch64.MemoryInit.BlockArgs s t column)
    (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s) : VG.Proof.Argon2.AArch64.MemoryInit.CallReady t := by
  have base := a.regs .x24 (by decide)
  have sp := a.sp
  refine ⟨by rw [sp]; exact h.stackMinimum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  digest : bytesAt t.mem (s.gpr .x22) 1024 = Spec.Argon2.hPrime 1024
    (bytesAt s.mem (s.gpr .x19) 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 (s.gpr .x20).toNat)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x22, 1024⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

theorem block_ok (v : HPrime.Backend) (name : String)
    (s : State) (column : Nat) (columnBound : column < 65536) (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s) :
    WP isa (VG.Impl.Argon2.AArch64.MemoryInit.block name v.hash column) s (fun t => VG.Proof.Argon2.AArch64.MemoryInit.BlockDone s t column) := by
  unfold VG.Impl.Argon2.AArch64.MemoryInit.block
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.blockArgs_ok s column columnBound
    (by simpa only [show BitVec.ofNat 64 64 = (64 : Addr) from rfl] using h.prefix 64 (by decide))
    (by simpa only [show BitVec.ofNat 64 68 = (68 : Addr) from rfl] using h.prefix 68 (by decide))).mono ?_)
  intro a ha
  refine (VG.Proof.Argon2.AArch64.MemoryInit.hPrime_call_ok v name a (ha.ready h) ha.inputLength ha.outputLength).mono ?_
  intro t ht
  refine ⟨?_, fun r hr => (ht.regs r hr).trans (ha.regs r hr),
    ht.sp.trans ha.sp, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
  · have digest := ht.digest
    rw [ha.output, ha.input, ha.mem, VG.Proof.Argon2.AArch64.MemoryInit.blockMem_bytes] at digest
    exact digest
  · have argsFrame : Frame [⟨s.gpr .x22, 1024⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem a.mem := by
      rw [ha.mem]
      exact (VG.Proof.Argon2.AArch64.MemoryInit.blockMem_frame _ _ _ _).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    apply argsFrame.trans
    have frame := ht.frame
    rw [ha.output, ha.work, ha.sp] at frame
    exact frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))

end VG.Proof.Argon2.AArch64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialLayout`. -/
section

/-! # The stack inputs and scratch allocation used by H₀ -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def slots : List Nat := [72, 80, 88, 96, 104, 112, 176, 184, 200, 208, 216, 224, 264]

def wordAt (s : State) (d : Nat) : Addr :=
  s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64

def inputRegion (s : State) (pointerOffset lengthOffset : Nat) : Region :=
  ⟨VG.Proof.Argon2.AArch64.Initial.wordAt s pointerOffset, (VG.Proof.Argon2.AArch64.Initial.wordAt s lengthOffset).toNat⟩

/-- Hash calls and argument preparation preserve these registers and bytes.
`x20` and `x22` are the running count and the current input length. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x20 → r ≠ .x22 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x24, 832⟩, below (s.sp) 16] s.mem t.mem

theorem Keeps.x24 {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Keeps s t) : t.gpr .x24 = s.gpr .x24 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.x19 {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Keeps s t) : t.gpr .x19 = s.gpr .x19 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.trans {s t u : State} (h : VG.Proof.Argon2.AArch64.Initial.Keeps s t) (k : VG.Proof.Argon2.AArch64.Initial.Keeps t u) : VG.Proof.Argon2.AArch64.Initial.Keeps s u :=
  ⟨fun r hr h1 h2 => (k.regs r hr h1 h2).trans (h.regs r hr h1 h2),
    k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.x24, h.sp] using k.frame)⟩

theorem Keeps.of_hash {s t : State} (h : HPrime.Keeps s t) : VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  refine ⟨?_, h.sp, h.rd, h.wr, h.frame⟩
  intro r hr _ _
  have hp : r ∈ preserved ∧ r ≠ .x30 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.regs r hp.1 hp.2

structure Space (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below (s.sp) 16)
  readable : ∀ d ∈ VG.Proof.Argon2.AArch64.Initial.slots, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8
  output : InRegions s.wr (s.gpr .x19) 64

theorem Space.keeps {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) : VG.Proof.Argon2.AArch64.Initial.Space t := by
  constructor
  · rw [k.sp]; exact h.stackMinimum
  · rw [k.x24, k.wr]; exact h.work
  · rw [k.x24, k.sp]; exact h.stackWork
  · rw [k.x19, k.x24]; exact h.frameWork
  · rw [k.x19, k.sp]; exact h.frameStack
  · intro d hd; rw [k.x19, k.rd, k.wr]; exact h.readable d hd
  · rw [k.x19, k.wr]; exact h.output

theorem Space.word_keeps {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t)
    (d : Nat) (hd : d + 8 ≤ 272) : VG.Proof.Argon2.AArch64.Initial.wordAt t d = VG.Proof.Argon2.AArch64.Initial.wordAt s d := by
  unfold VG.Proof.Argon2.AArch64.Initial.wordAt
  rw [k.x19]
  apply k.frame.readW (r := ⟨s.gpr .x19, 272⟩)
    (Offset.contains_base _ hd (by omega)) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
  · exact h.frameStack

theorem Space.write {s : State} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (d n : Nat) (hd : d + n ≤ 16384) :
    InRegions s.wr (s.gpr .x24 + BitVec.ofNat 64 d) n :=
  ⟨_, h.work, Offset.contains_base _ hd (by omega)⟩

theorem Space.input_keeps {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t)
    (po lo : Nat) (hp : po + 8 ≤ 272) (hl : lo + 8 ≤ 272) :
    VG.Proof.Argon2.AArch64.Initial.inputRegion t po lo = VG.Proof.Argon2.AArch64.Initial.inputRegion s po lo := by
  simp only [VG.Proof.Argon2.AArch64.Initial.inputRegion, h.word_keeps k po hp, h.word_keeps k lo hl]

theorem Keeps.bytes {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Keeps s t) (r : Region)
    (work : r.Disjoint ⟨s.gpr .x24, 16384⟩)
    (stack : r.Disjoint (below (s.sp) 16)) (bound : r.len ≤ 2 ^ 64) :
    bytesAt t.mem r.base r.len = bytesAt s.mem r.base r.len := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := r) _ bound hi
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact work.sub_right (Region.sub_prefix (by decide))
  · exact stack

end VG.Proof.Argon2.AArch64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitFill`. -/
section

section

/-! Merged from `Proof.Argon2.AArch64.MemoryInitMatrix`. -/
section
/-! # Matrix cells and the memory preserved by initialization calls -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
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

theorem BlockDone.h0 {s t : State} {column : Nat} (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockDone s t column)
    (ready : VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s) : bytesAt t.mem (s.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .x19, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ready.frameOutput.sub_left (Region.sub_prefix (by decide))
  · exact ready.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact ready.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem BlockDone.block {s t : State} {column : Nat} (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockDone s t column) :
    blockAt t.mem (s.gpr .x22) = parseBlock
      (Proof.Argon2.initialBytes (bytesAt s.mem (s.gpr .x19) 64) (s.gpr .x20).toNat column) :=
  Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ h.digest

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Permissions for the matrix, derivation frame and hash scratch -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64

structure Space (s : State) (memory : Addr) (bytes : Nat) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  matrix : Covers [⟨memory, bytes⟩] s.wr
  frame : Covers [⟨s.gpr .x19, 72⟩] s.wr
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  frameMatrix : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨memory, bytes⟩
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  matrixWork : (⟨memory, bytes⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackFrame : (below (s.sp) 16).Disjoint ⟨s.gpr .x19, 272⟩
  stackMatrix : (below (s.sp) 16).Disjoint ⟨memory, bytes⟩
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩
  bound : bytes < 2 ^ 64

theorem Space.same {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory bytes)
    (wr : t.wr = s.wr) (bp : t.gpr .x19 = s.gpr .x19)
    (bx : t.gpr .x24 = s.gpr .x24) (sp : t.sp = s.sp) : VG.Proof.Argon2.AArch64.MemoryInit.Space t memory bytes := by
  constructor
  · rw [sp]; exact h.stackMinimum
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
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory bytes) (dst : s.gpr .x22 = memory + BitVec.ofNat 64 d)
    (bound : d + 1024 ≤ bytes) : VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s := by
  have outputSub : Region.Sub ⟨s.gpr .x22, 1024⟩ ⟨memory, bytes⟩ := by
    rw [dst]; exact Offset.sub_base _ bound
  have outputCover : Covers [⟨s.gpr .x22, 1024⟩] s.wr := by
    have narrow : Covers [⟨s.gpr .x22, 1024⟩] [⟨memory, bytes⟩] := Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, d, dst, bound⟩)
    exact fun p n hp => h.matrix p n (narrow p n hp)
  exact ⟨h.stackMinimum, h.frame, outputCover, h.work,
    h.frameWork.sub_left (Region.sub_prefix (by decide)),
    (h.frameMatrix.sub_left (Region.sub_prefix (by decide))).sub_right outputSub,
    h.matrixWork.sub_left outputSub,
    h.stackFrame.sub_right (Region.sub_prefix (by decide)),
    h.stackMatrix.sub_right outputSub, h.stackWork⟩

end VG.Proof.Argon2.AArch64.MemoryInit

end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitSteps`. -/
section
/-! Public pointer advances and lane countdowns. -/
namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64

structure Advanced (s t : State) : Prop where
  destination : t.gpr .x22 = s.gpr .x22 + 1024
  other : ∀ r, r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem advance_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten) s (VG.Proof.Argon2.AArch64.MemoryInit.Advanced s) := by
  refine (Instructions.addi_ok s .x22 1024 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨value, k⟩
  refine ⟨value, fun r h1 h2 h3 => k.regs r ?_, k.mem, k.rd, k.wr, k.sp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1,h2,h3⟩

structure LaneEnd (s t : State) : Prop where
  destination : t.gpr .x22 = s.gpr .x22 + s.gpr .x21 - 1024
  lane : t.gpr .x20 = s.gpr .x20 + 1
  remaining : t.gpr .x23 = s.gpr .x23 - 1
  flag : t.gpr .x15 = s.gpr .x23 - 1
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem laneEnd_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.add .x22 .x21,
      Impl.Argon2.AArch64.Instructions.subi .x22 1024,
      Impl.Argon2.AArch64.Instructions.addi .x20 1,
      Impl.Argon2.AArch64.Instructions.subi .x23 1].flatten) s (VG.Proof.Argon2.AArch64.MemoryInit.LaneEnd s) := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine (Instructions.add_ok s .x22 .x21 (by decide)).mono ?_
  rintro a ⟨dstA, ka⟩
  rw [WP.block_append_iff]
  refine (Instructions.subi_ok a .x22 1024 (by decide) (by decide) (by decide)).mono ?_
  rintro b ⟨dstB, _, kb⟩
  rw [WP.block_append_iff]
  refine (Instructions.addi_ok b .x20 1 (by decide) (by decide) (by decide)).mono ?_
  rintro c ⟨laneC, kc⟩
  refine (Instructions.subi_ok c .x23 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨remaining, flag, kt⟩
  have remainingC : c.gpr .x23 = s.gpr .x23 :=
    (kc.regs _ (by decide)).trans ((kb.regs _ (by decide)).trans (ka.regs _ (by decide)))
  refine ⟨?_, ?_, remaining.trans (congrArg (· - 1) remainingC),
    flag.trans (congrArg (· - 1) remainingC), ?_,
    kt.mem.trans (kc.mem.trans (kb.mem.trans ka.mem)),
    kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
    kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)),
    kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
  · rw [kt.regs .x22 (by decide), kc.regs .x22 (by decide), dstB, dstA]; rfl
  · rw [kt.regs .x20 (by decide), laneC, kb.regs .x20 (by decide), ka.regs .x20 (by decide)]; rfl
  · intro r h1 h2 h3 h4 h5
    have hka : r ∉ [Reg.x22, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h5⟩
    have hkb : r ∉ [Reg.x22, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h4,h5⟩
    have hkc : r ∉ [Reg.x20, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h2,h4,h5⟩
    have hkt : r ∉ [Reg.x23, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h3,h4,h5⟩
    exact (kt.regs r hkt).trans ((kc.regs r hkc).trans ((kb.regs r hkb).trans (ka.regs r hka)))
end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitLane`. -/
section
/-! # Initializing both leading blocks of one lane -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LaneDone (s t : State) : Prop where
  first : bytesAt t.mem (s.gpr .x22) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .x19) 64) (s.gpr .x20).toNat 0
  second : bytesAt t.mem (s.gpr .x22 + 1024) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .x19) 64) (s.gpr .x20).toNat 1
  destination : t.gpr .x22 = s.gpr .x22 + s.gpr .x21
  lane : t.gpr .x20 = s.gpr .x20 + 1
  remaining : t.gpr .x23 = s.gpr .x23 - 1
  flag : t.gpr .x15 = s.gpr .x23 - 1
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x22, 2048⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

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

theorem lane_ok (v : HPrime.Backend) (name : String)
    (s : State) (memory : Addr) (bytes d : Nat) (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory bytes)
    (dst : s.gpr .x22 = memory + BitVec.ofNat 64 d) (bound : d + 2048 ≤ bytes) :
    WP isa (lane name v.hash) s (VG.Proof.Argon2.AArch64.MemoryInit.LaneDone s) := by
  have ready := space.blockReady dst (by omega)
  unfold lane
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.block_ok v name s 0 (by decide) ready).mono ?_)
  intro a ha
  have spaceA := space.same ha.wr (ha.regs .x19 (by decide))
    (ha.regs .x24 (by decide)) ha.sp
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.advance_ok a).mono ?_)
  intro b hb
  have spaceB := spaceA.same hb.wr (hb.other .x19 (by decide) (by decide) (by decide))
    (hb.other .x24 (by decide) (by decide) (by decide)) hb.sp
  have base : b.gpr .x22 = s.gpr .x22 + 1024 := by rw [hb.destination, ha.regs .x22 (by decide)]
  have bp : b.gpr .x19 = s.gpr .x19 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have bx : b.gpr .x24 = s.gpr .x24 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have sp : b.sp = s.sp := hb.sp.trans ha.sp
  have laneB : b.gpr .x20 = s.gpr .x20 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have strideB : b.gpr .x21 = s.gpr .x21 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have remainingB : b.gpr .x23 = s.gpr .x23 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have dstB : b.gpr .x22 = memory + BitVec.ofNat 64 (d + 1024) := by
    rw [base, dst, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have readyB := spaceB.blockReady dstB (by omega)
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.block_ok v name b 1 (by decide) readyB).mono ?_)
  intro c hc
  refine (VG.Proof.Argon2.AArch64.MemoryInit.laneEnd_ok c).mono ?_
  intro t ht
  have secondFrame := hc.frame
  rw [base, bx, sp, bp] at secondFrame
  have keptFirst : bytesAt c.mem (s.gpr .x22) 1024 = bytesAt b.mem (s.gpr .x22) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply secondFrame.bytes (R := ⟨s.gpr .x22, 1024⟩) _
      (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · rw [dst]; exact space.matrixWork.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.stackMatrix.symm.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.frameMatrix.symm.sub_left (Offset.sub_base _ (by omega)) |>.sub_right
        (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
  have h0B : bytesAt b.mem (b.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
    rw [hb.mem, bp]; exact ha.h0 ready
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.sp.trans (hc.sp.trans (hb.sp.trans ha.sp)), ht.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),
    ht.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)), ?_⟩
  · rw [ht.mem, keptFirst, hb.mem]; exact ha.digest
  · have digest := hc.digest
    rw [base, h0B, laneB] at digest
    rw [ht.mem]; exact digest
  · rw [ht.destination, hc.regs .x22 (by decide), hc.regs .x21 (by decide), base, strideB]
    rw [BitVec.add_assoc, BitVec.add_comm (1024 : Addr), ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  · rw [ht.lane, hc.regs .x20 (by decide), laneB]
  · rw [ht.remaining, hc.regs .x23 (by decide), remainingB]
  · rw [ht.flag, hc.regs .x23 (by decide), remainingB]
  · intro r hr h14 h12 h15
    have h12temp : r ≠ .x12 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h15temp : r ≠ .x15 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r h14 h12 h15 h12temp h15temp).trans ((hc.regs r hr).trans
      ((hb.other r h14 h12temp h15temp).trans (ha.regs r hr)))
  · rw [ht.mem]
    rw [hb.mem] at secondFrame
    have firstFrame := VG.Proof.Argon2.AArch64.MemoryInit.frame_widen (p := s.gpr .x22) (d := 0)
      (by simpa using ha.frame)
      (by decide)
    have finalFrame := VG.Proof.Argon2.AArch64.MemoryInit.frame_widen (p := s.gpr .x22) (d := 1024)
      (by simpa only [show BitVec.ofNat 64 1024 = (1024 : Addr) from rfl] using secondFrame) (by decide)
    exact firstFrame.trans finalFrame

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitStage`. -/
section
/-! # Matrix invariant: completed lanes contain their RFC initialization blocks -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
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
    VG.Proof.Argon2.AArch64.MemoryInit.Initialized (clearMem m base (128 * (lanes * q))) base lanes q 0 h0 := by
  intro lane hl column hc
  rw [VG.Proof.Argon2.AArch64.MemoryInit.clearMem_block _ _ _ _ bound (VG.Proof.Argon2.AArch64.MemoryInit.cell_bound _ _ _ _ hl hc)]
  simp only [Nat.not_lt_zero, false_and, ite_false]

theorem initialized_lane {s t : State} (memory : Addr) (lanes q j : Nat)
    (h0 : List Byte) (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory (1024 * (lanes * q)))
    (hq : 2 ≤ q) (hj : j < lanes) (lanesBound : lanes < 2 ^ 64)
    (dst : s.gpr .x22 = memory + BitVec.ofNat 64 (1024 * (j * q)))
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 j)
    (hash : bytesAt s.mem (s.gpr .x19) 64 = h0)
    (initialized : VG.Proof.Argon2.AArch64.MemoryInit.Initialized s.mem memory lanes q j h0) (done : VG.Proof.Argon2.AArch64.MemoryInit.LaneDone s t) :
    VG.Proof.Argon2.AArch64.MemoryInit.Initialized t.mem memory lanes q (j + 1) h0 := by
  have laneValue : (s.gpr .x20).toNat = j := by
    rw [laneReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have currentEnd : 1024 * (j * q) + 2048 ≤ 2 ^ 64 := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    have b := space.bound
    omega
  have cellEnd (lane column : Nat) (hl : lane < lanes) (hc : column < q) :
      1024 * (lane * q + column) + 1024 ≤ 2 ^ 64 := by
    have cell := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q lane column hl hc
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
        have sep := VG.Proof.Argon2.AArch64.MemoryInit.cell_sep q j j column hq hc (Or.inr large)
        have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) =
            blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) := by
          apply VG.Proof.Argon2.AArch64.MemoryInit.blockAt_frame done.frame
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [dst]; exact Offset.disjoint _ sep (cellEnd j column hj hc) currentEnd
          · exact space.matrixWork.sub_left (Offset.sub_base _
              (by have := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q j column hj hc; omega))
          · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
              (by have := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q j column hj hc; omega))
          · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
              (by have := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q j column hj hc; omega)) |>.sub_right
              (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
        rw [kept, initialized j hj column hc]
        simp only [Nat.lt_irrefl, false_and, ite_false, ite_eq_right (by omega : ¬ (j < j + 1 ∧ column < 2))]
  · have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) =
        blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) := by
      apply VG.Proof.Argon2.AArch64.MemoryInit.blockAt_frame done.frame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [dst]
        exact Offset.disjoint _ (VG.Proof.Argon2.AArch64.MemoryInit.cell_sep q j lane column hq hc (Or.inl same))
          (cellEnd lane column hl hc) currentEnd
      · exact space.matrixWork.sub_left (Offset.sub_base _
          (by have := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q lane column hl hc; omega))
      · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
          (by have := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q lane column hl hc; omega))
      · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
          (by have := VG.Proof.Argon2.AArch64.MemoryInit.cell_bound lanes q lane column hl hc; omega)) |>.sub_right
          (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
    rw [kept, initialized lane hl column hc]
    by_cases before : lane < j ∧ column < 2 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitSetup`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitClearSetup`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitClear`. -/
section
/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

theorem decrement_ok (s : State) :
    WP isa (.block (Impl.Argon2.AArch64.Instructions.subi .x8 1)) s fun t =>
      t.gpr .x8 = s.gpr .x8 - 1 ∧ t.gpr .x15 = s.gpr .x8 - 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.subi,
    Impl.Argon2.AArch64.Instructions.sub, Impl.Argon2.AArch64.Instructions.imm,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    show 1 < 65536 from by decide, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (1#16).setWidth 64 = 1#64 from rfl,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, sub_value, Bool.toNat_true,
    BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem clearWord_ok (s : State) (hw : InRegions s.wr (s.gpr .x22) 8) :
    WP isa (.block clearWord) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x22) (s.gpr .x3) ∧
      t.gpr .x22 = s.gpr .x22 + 8 ∧ t.gpr .x8 = s.gpr .x8 - 1 ∧
      t.gpr .x15 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x8 → r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [clearWord, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  have hw' : InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 0) 8 := by
    simpa only [BitVec.add_zero] using hw
  refine (Instructions.store_ok s .x22 .x3 0 (by decide) (by decide) hw').mono ?_
  rintro a ⟨memA, regsA, rdA, wrA, spA⟩
  rw [WP.block_append_iff]
  refine (Instructions.addi_ok a .x22 8 (by decide) (by decide) (by decide)).mono ?_
  rintro b ⟨dst, kb⟩
  refine (VG.Proof.Argon2.AArch64.MemoryInit.decrement_ok b).mono ?_
  rintro t ⟨count, flag, kt⟩
  have countB : b.gpr .x8 = s.gpr .x8 := (kb.regs _ (by decide)).trans (congrFun regsA _)
  refine ⟨?_, ?_, count.trans (congrArg (· - 1) countB),
    flag.trans (congrArg (· - 1) countB), ?_, kt.rd.trans (kb.rd.trans rdA),
    kt.wr.trans (kb.wr.trans wrA), kt.sp.trans (kb.sp.trans spA)⟩
  · rw [kt.mem, kb.mem, memA]
    rw [BitVec.add_zero]
  · rw [kt.regs .x22 (by decide), dst, regsA]
    rfl
  · intro r h1 h2 h3 h4
    exact (kt.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h3,h4⟩)).trans
      ((kb.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h2,h3,h4⟩)).trans
        (congrFun regsA r))

structure ClearI (s₀ : State) (p : Addr) (n j : Nat) (s : State) : Prop where
  bound : j ≤ n
  destination : s.gpr .x22 = p + BitVec.ofNat 64 (8 * j)
  count : s.gpr .x8 = BitVec.ofNat 64 (n - j)
  zero : s.gpr .x3 = 0
  other : ∀ r, r ≠ .x8 → r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = clearMem s₀.mem p j

theorem clearLoop_ok (s₀ : State) (p : Addr) (n : Nat) (lo : 1 ≤ n)
    (bound : 8 * n < 2 ^ 64) (dst : s₀.gpr .x22 = p)
    (count : s₀.gpr .x8 = BitVec.ofNat 64 n) (zero : s₀.gpr .x3 = 0)
    (write : ∀ j < n, InRegions s₀.wr (p + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.loop (.block clearWord) (.nonzero .x .x15)) s₀ (VG.Proof.Argon2.AArch64.MemoryInit.ClearI s₀ p n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ VG.Proof.Argon2.AArch64.MemoryInit.ClearI s₀ p n j s)
    ?_ n s₀ ⟨0, by omega, lo, by omega, by simpa using dst, by simpa only [Nat.sub_zero] using count,
      zero, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k s ⟨j, rfl, hj, h⟩
  have hw : InRegions s.wr (s.gpr .x22) 8 := by
    rw [h.wr, h.destination]; exact write j hj
  refine (VG.Proof.Argon2.AArch64.MemoryInit.clearWord_ok s hw).mono ?_
  rintro t ⟨memT, dstT, countT, zfT, otherT, rdT, wrT, spT⟩
  have nextCount : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : VG.Proof.Argon2.AArch64.MemoryInit.ClearI s₀ p n (j + 1) t := by
    refine ⟨by omega, ?_, ?_, (otherT _ (by decide) (by decide) (by decide) (by decide)).trans h.zero,
      fun r h1 h2 h3 h4 => (otherT r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4),
      rdT.trans h.rd, wrT.trans h.wr, spT.trans h.sp, ?_⟩
    · rw [dstT, h.destination, BitVec.add_assoc, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 2
    · rw [countT, h.count, nextCount]
    · rw [memT, h.mem, h.destination, h.zero]; rfl
  have eqzero : BitVec.ofNat 64 (n - (j + 1)) = 0 ↔ n - (j + 1) = 0 := by
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  have flag : eval (.nonzero .x .x15) t = some (decide (n - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, zfT, h.count, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
    exact not_congr eqzero
  by_cases done : j + 1 = n
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show n - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using flag
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega : n - (j + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Clearing the complete allocation using its public block count -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure ClearHeader (s t : State) : Prop where
  destination : t.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset
  count : t.gpr .x8 = VG.Proof.Argon2.AArch64.Initial.wordAt s blocksOffset
  zero : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clearHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8) :
    WP isa (.block clearHeader) s (VG.Proof.Argon2.AArch64.MemoryInit.ClearHeader s) := by
  have hm : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232#64) 8 := memoryRead
  have hb : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240#64) 8 := blocksRead
  apply WP.of_runBlock
  simp only [clearHeader, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.imm, show 0 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod, memoryOffset, blocksOffset,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, hm, hb, reduceCtorEq, ite_true, ite_false, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r h1 h2 h3 _ _
    simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure ClearSetup (s t : State) : Prop where
  destination : t.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset
  count : t.gpr .x8 = VG.Proof.Argon2.AArch64.Initial.wordAt s blocksOffset * 128
  zero : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clearSetup_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8) :
    WP isa clearSetupCode s (VG.Proof.Argon2.AArch64.MemoryInit.ClearSetup s) := by
  unfold clearSetupCode clearSetup
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.AArch64.MemoryInit.clearHeader_ok s memoryRead blocksRead).mono ?_
  intro a ha
  refine (scale_ok a .x8 7).mono ?_
  intro b hb
  exact ⟨(hb.other _ (by decide) (by decide)).trans ha.destination,
    by rw [hb.value, ha.count]; rfl,
    (hb.other _ (by decide) (by decide)).trans ha.zero,
    fun r h1 h2 h3 h4 h5 => (hb.other r h2 h5).trans (ha.other r h1 h2 h3 h4 h5),
    hb.mem.trans ha.mem, hb.rd.trans ha.rd, hb.wr.trans ha.wr, hb.sp.trans ha.sp⟩

structure Cleared (s t : State) (memory : Addr) (blocks : Nat) : Prop where
  destination : t.gpr .x22 = memory + BitVec.ofNat 64 (1024 * blocks)
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = clearMem s.mem memory (128 * blocks)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clear_ok (s : State) (memory : Addr) (blocks : Nat) (lo : 1 ≤ blocks)
    (bound : 1024 * blocks < 2 ^ 64)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8)
    (memoryWord : VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset = memory)
    (blocksWord : VG.Proof.Argon2.AArch64.Initial.wordAt s blocksOffset = BitVec.ofNat 64 blocks)
    (cover : Covers [⟨memory, 1024 * blocks⟩] s.wr) :
    WP isa clear s fun t => VG.Proof.Argon2.AArch64.MemoryInit.Cleared s t memory blocks := by
  unfold clear
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.clearSetup_ok s memoryRead blocksRead).mono ?_)
  intro b hb
  have count : b.gpr .x8 = BitVec.ofNat 64 (128 * blocks) := by
    rw [hb.count, blocksWord, show (128 : Addr) = BitVec.ofNat 64 128 from rfl,
      ← BitVec.ofNat_mul, Nat.mul_comm]
  have dst : b.gpr .x22 = memory := hb.destination.trans memoryWord
  have zero := hb.zero
  have mem := hb.mem
  have rd := hb.rd
  have wr := hb.wr
  have other := hb.other
  have sp := hb.sp
  refine (VG.Proof.Argon2.AArch64.MemoryInit.clearLoop_ok b memory (128 * blocks) (by omega) (by omega) dst count zero ?_).mono ?_
  · intro j hj
    rw [wr]
    exact cover _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · intro t ht
    refine ⟨?_, fun r h1 h2 h3 h4 h5 => (ht.other r h2 h1 h4 h5).trans (other r h1 h2 h3 h4 h5), ?_,
      ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    · rw [ht.destination, show 8 * (128 * blocks) = 1024 * blocks by omega]
    · rw [ht.mem, mem]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Set up the public lane loop after matrix clearing -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure LanesHeader (s t : State) : Prop where
  destination : t.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset
  lane : t.gpr .x20 = 0
  remaining : t.gpr .x23 = VG.Proof.Argon2.AArch64.Initial.wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lanesHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8) :
    WP isa (.block lanesHeader) s (VG.Proof.Argon2.AArch64.MemoryInit.LanesHeader s) := by
  have hm : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232#64) 8 := memoryRead
  have hl : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184#64) 8 := lanesRead
  apply WP.of_runBlock
  simp only [lanesHeader, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.imm, show 0 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod, memoryOffset,
    VG.Impl.Argon2.AArch64.Initial.lanesOffset,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, hm, hl, reduceCtorEq, ite_true, ite_false, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r h1 h2 h3 _
    simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure Setup (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  destination : t.gpr .x22 = memory
  lane : t.gpr .x20 = 0
  remaining : t.gpr .x23 = BitVec.ofNat 64 lanes
  stride : t.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x21 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lanesSetup_ok (s : State) (memory : Addr) (lanes q : Nat)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8)
    (memoryWord : VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset = memory)
    (lanesWord : VG.Proof.Argon2.AArch64.Initial.wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (laneLength : s.gpr .x21 = BitVec.ofNat 64 q) :
    WP isa (.block lanesSetup) s fun t => VG.Proof.Argon2.AArch64.MemoryInit.Setup s t memory lanes q := by
  unfold lanesSetup
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.AArch64.MemoryInit.lanesHeader_ok s memoryRead lanesRead).mono ?_
  intro a ha
  refine (scale_ok a .x21 10).mono ?_
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => (ht.other r h4 h5).trans (ha.other r h1 h2 h3 h5),
    ht.mem.trans ha.mem, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  · rw [ht.other .x22 (by decide) (by decide), ha.destination, memoryWord]
  · rw [ht.other .x20 (by decide) (by decide), ha.lane]
  · rw [ht.other .x23 (by decide) (by decide), ha.remaining, lanesWord]
  · rw [ht.value, ha.other .x21 (by decide) (by decide) (by decide) (by decide), laneLength,
      ← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitLoop`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitFrame`. -/
section
/-! # Effects allowed across the complete lane loop -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Spec.Blake2 (bytesAt)

def keptRegs : List Reg := [.x19, .x24, .x21, .x25, .x26, .x27, .x28]

structure Keeps (s t : State) (memory : Addr) (bytes : Nat) : Prop where
  regs : ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.keptRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, bytes⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

theorem Keeps.x19 {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s t memory bytes) :
    t.gpr .x19 = s.gpr .x19 := h.regs _ (by decide)
theorem Keeps.x24 {s t : State} {memory : Addr} {bytes : Nat} (h : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s t memory bytes) :
    t.gpr .x24 = s.gpr .x24 := h.regs _ (by decide)
theorem Keeps.refl (s : State) (memory : Addr) (bytes : Nat) : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s s memory bytes :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {s t u : State} {memory : Addr} {bytes : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s t memory bytes) (k : VG.Proof.Argon2.AArch64.MemoryInit.Keeps t u memory bytes) : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s u memory bytes :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.x24, h.sp, h.x19] using k.frame)⟩

theorem Space.keeps {s t : State} {memory : Addr} {bytes : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory bytes) (k : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s t memory bytes) : VG.Proof.Argon2.AArch64.MemoryInit.Space t memory bytes :=
  h.same k.wr k.x19 k.x24 k.sp

theorem Keeps.h0 {s t : State} {memory : Addr} {bytes : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s t memory bytes) (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory bytes) :
    bytesAt t.mem (t.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
  rw [h.x19]
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .x19, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact space.frameMatrix.sub_left (Region.sub_prefix (by decide))
  · exact space.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact space.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem LaneDone.keeps {s t : State} (memory : Addr) (bytes d : Nat)
    (h : VG.Proof.Argon2.AArch64.MemoryInit.LaneDone s t) (dst : s.gpr .x22 = memory + BitVec.ofNat 64 d)
    (bound : d + 2048 ≤ bytes) : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s t memory bytes := by
  refine ⟨?_, h.sp, h.rd, h.wr, ?_⟩
  · intro r hr
    have facts : ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.keptRegs, r ∈ FillCompress.loopRegs ∧ r ≠ .x22 ∧ r ≠ .x20 ∧ r ≠ .x23 := by decide
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

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Termination and correctness of the all-lanes initialization loop -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopI (s₀ : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte) (s : State) : Prop where
  bound : j ≤ lanes
  destination : s.gpr .x22 = memory + BitVec.ofNat 64 (1024 * (j * q))
  lane : s.gpr .x20 = BitVec.ofNat 64 j
  remaining : s.gpr .x23 = BitVec.ofNat 64 (lanes - j)
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  keeps : VG.Proof.Argon2.AArch64.MemoryInit.Keeps s₀ s memory (1024 * (lanes * q))
  initialized : VG.Proof.Argon2.AArch64.MemoryInit.Initialized s.mem memory lanes q j h0
  hash : bytesAt s.mem (s.gpr .x19) 64 = h0

theorem lane_step (v : HPrime.Backend) (name : String)
    (s₀ s : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte)
    (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s₀ memory (1024 * (lanes * q))) (hj : j < lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (h : VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₀ memory lanes q j h0 s) :
    WP isa (lane name v.hash) s fun t =>
      VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₀ memory lanes q (j + 1) h0 t ∧
      eval (.nonzero .x .x15) t = some (decide (lanes - (j + 1) ≠ 0)) := by
  have spaceS := space.keeps h.keeps
  have endBound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  refine (VG.Proof.Argon2.AArch64.MemoryInit.lane_ok v name s memory (1024 * (lanes * q)) (1024 * (j * q))
    spaceS h.destination endBound).mono ?_
  intro t ht
  have kt := ht.keeps memory _ _ h.destination endBound
  have nextCount : BitVec.ofNat 64 (lanes - j) - 1 = BitVec.ofNat 64 (lanes - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₀ memory lanes q (j + 1) h0 t := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, h.keeps.trans kt,
      VG.Proof.Argon2.AArch64.MemoryInit.initialized_lane memory lanes q j h0 spaceS hq hj lanesBound h.destination h.lane
        h.hash h.initialized ht, (kt.h0 spaceS).trans h.hash⟩
    · rw [ht.destination, h.destination, h.stride, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_mul, Nat.one_mul, Nat.mul_add]
    · rw [ht.lane, h.lane, BitVec.ofNat_add]; rfl
    · rw [ht.remaining, h.remaining, nextCount]
    · exact (kt.regs .x21 (by decide)).trans h.stride
  have eqzero : BitVec.ofNat 64 (lanes - (j + 1)) = 0 ↔ lanes - (j + 1) = 0 := by
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lanes - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  have zf : eval (.nonzero .x .x15) t = some (decide (lanes - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, ht.flag, h.remaining, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
    exact not_congr eqzero
  exact ⟨next, zf⟩


theorem lanesLoop_ok (v : HPrime.Backend) (name : String)
    (s₀ : State) (memory : Addr) (lanes q : Nat) (h0 : List Byte)
    (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s₀ memory (1024 * (lanes * q))) (lo : 1 ≤ lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (dst : s₀.gpr .x22 = memory) (laneReg : s₀.gpr .x20 = 0)
    (remaining : s₀.gpr .x23 = BitVec.ofNat 64 lanes)
    (stride : s₀.gpr .x21 = BitVec.ofNat 64 (1024 * q))
    (initialized : VG.Proof.Argon2.AArch64.MemoryInit.Initialized s₀.mem memory lanes q 0 h0)
    (hash : bytesAt s₀.mem (s₀.gpr .x19) 64 = h0) :
    WP isa (.loop (lane name v.hash) (.nonzero .x .x15)) s₀ (VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₀ memory lanes q lanes h0) := by
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = lanes - j ∧ j < lanes ∧ VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₀ memory lanes q j h0 s)
    ?_ lanes s₀ ⟨0, by omega, lo, by omega, by simpa using dst, laneReg,
      by simpa only [Nat.sub_zero] using remaining, stride, Keeps.refl _ _ _, initialized, hash⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine (VG.Proof.Argon2.AArch64.MemoryInit.lane_step v name s₀ s memory lanes q j h0 space hj lanesBound hq h).mono ?_
  intro t ⟨next, zf⟩
  by_cases done : j + 1 = lanes
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show lanes - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using zf
  · refine .inr ⟨?_, lanes - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [zf]
    exact congrArg some (decide_eq_true (by omega : lanes - (j + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInit`. -/
section
/-! # Functional correctness of complete memory initialization -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)
open VG.Spec.Blake2 (bytesAt)

theorem Cleared.frame {s t : State} {memory : Addr} {blocks : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Cleared s t memory blocks) (bound : 1024 * blocks < 2 ^ 64) :
    Frame [⟨memory, 1024 * blocks⟩] s.mem t.mem := by
  rw [h.mem]
  simpa only [show 8 * (128 * blocks) = 1024 * blocks by omega] using
    clearMem_frame s.mem memory (128 * blocks) (by omega)

theorem Cleared.word {s t : State} {memory : Addr} {blocks d : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Cleared s t memory blocks) (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory (1024 * blocks))
    (offset : d + 8 ≤ 272) : VG.Proof.Argon2.AArch64.Initial.wordAt t d = VG.Proof.Argon2.AArch64.Initial.wordAt s d := by
  unfold VG.Proof.Argon2.AArch64.Initial.wordAt
  rw [h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]
  apply (h.frame space.bound).readW (r := ⟨s.gpr .x19, 272⟩)
    (Offset.contains_base _ offset (by omega)) ?_ (by decide)
  intro r hr; simp only [List.mem_singleton] at hr; subst r
  exact space.frameMatrix

theorem code_ok (v : HPrime.Backend) (name : String)
    (s : State) (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (hq : 2 ≤ q)
    (lanesBound : lanes < 2 ^ 64) (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory (1024 * (lanes * q)))
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8)
    (memoryWord : VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset = memory)
    (lanesWord : VG.Proof.Argon2.AArch64.Initial.wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (blocksWord : VG.Proof.Argon2.AArch64.Initial.wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q))
    (laneLength : s.gpr .x21 = BitVec.ofNat 64 q) :
    WP isa (VG.Impl.Argon2.AArch64.MemoryInit.code name v.hash) s fun t =>
      VG.Proof.Argon2.AArch64.MemoryInit.Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .x19) 64) ∧
      t.gpr .x19 = s.gpr .x19 ∧ t.gpr .x24 = s.gpr .x24 ∧ t.sp = s.sp ∧
      t.gpr .x21 = BitVec.ofNat 64 (1024 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem ∧
      (∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r) := by
  unfold VG.Impl.Argon2.AArch64.MemoryInit.code lanesSetupCode
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.clear_ok s memory (lanes * q) blocksPositive space.bound memoryRead
    blocksRead memoryWord blocksWord space.matrix).mono ?_)
  intro a ha
  have bpA := ha.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bxA := ha.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have spA := ha.sp
  have spaceA := space.same ha.wr bpA bxA spA
  have hashA : bytesAt a.mem (a.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
    rw [bpA]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact (ha.frame space.bound).bytes (R := ⟨s.gpr .x19, 64⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact space.frameMatrix.sub_left (Region.sub_prefix (by decide)))
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine WP.seq ((VG.Proof.Argon2.AArch64.MemoryInit.lanesSetup_ok a memory lanes q
    (by rw [ha.rd, ha.wr, bpA]; exact memoryRead)
    (by rw [ha.rd, ha.wr, bpA]; exact lanesRead)
    ((ha.word space (by decide)).trans memoryWord)
    ((ha.word space (by decide)).trans lanesWord)
    ((ha.other .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans laneLength)).mono ?_)
  intro b hb
  have bpB := hb.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bxB := hb.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have spB := hb.sp
  have spaceB := spaceA.same hb.wr bpB bxB spB
  refine (VG.Proof.Argon2.AArch64.MemoryInit.lanesLoop_ok v name b memory lanes q (bytesAt s.mem (s.gpr .x19) 64)
    spaceB lo lanesBound hq hb.destination hb.lane hb.remaining hb.stride ?_ ?_).mono ?_
  · rw [hb.mem, ha.mem]
    exact VG.Proof.Argon2.AArch64.MemoryInit.initialized_zero s.mem memory lanes q space.bound _
  · rw [hb.mem, bpB]; exact hashA
  · intro t ht
    refine ⟨ht.initialized, ht.keeps.x19.trans (bpB.trans bpA),
      ht.keeps.x24.trans (bxB.trans bxA), ht.keeps.sp.trans (spB.trans spA),
      (ht.keeps.regs .x21 (by decide)).trans hb.stride, ht.keeps.rd.trans (hb.rd.trans ha.rd), ht.keeps.wr.trans (hb.wr.trans ha.wr), ?_⟩
    have unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r := by
      intro r hr
      have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
          r ∈ VG.Proof.Argon2.AArch64.MemoryInit.keptRegs ∧ r ≠ .x22 ∧ r ≠ .x8 ∧ r ≠ .x3 ∧ r ≠ .x12 ∧ r ≠ .x15 ∧
          r ≠ .x20 ∧ r ≠ .x23 ∧ r ≠ .x21 := by decide
      obtain ⟨member, h22, h8, h3, h12, h15, h20, h23, h21⟩ := facts r hr
      exact (ht.keeps.regs r member).trans
        ((hb.other r h22 h20 h23 h21 h15).trans (ha.other r h22 h8 h3 h12 h15))
    have fb : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem b.mem := by
      rw [hb.mem]
      exact (ha.frame space.bound).mono (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact List.mem_cons_self ..)
    refine ⟨?_, unused⟩
    apply fb.trans
    have f := ht.keeps.frame
    rw [bpB, bpA, bxB, bxA, spB, spA] at f
    exact f

/-- Every cell agrees with the reviewed initialization spec, in lane-major order. -/
theorem Initialized.spec {m : Mem} {base : Addr} {p : Spec.Argon2.Params}
    {h0 : List Byte} (hl : 0 < p.lanes) (hq : 0 < p.laneLen)
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Initialized m base p.lanes p.laneLen p.lanes h0)
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

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitRepresent`. -/
section
/-! Memory initialization establishes the shared matrix representation invariant. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.Spec.Argon2

theorem Initialized.represents {m : Mem} {base : Addr} {p : Params} {h0 : List Byte}
    (positive : 0 < p.lanes) (lanePositive : 0 < p.laneLen)
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Initialized m base p.lanes p.laneLen p.lanes h0) :
    Proof.Argon2.Represents m base p.blocks (initMemory p h0).memory := by
  refine ⟨Proof.Argon2.initMemory_size p h0, ?_⟩
  intro k hk
  rw [Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk), Option.getD_some]
  unfold Proof.Argon2.matrixCell
  rw [Nat.mul_comm k 1024]
  exact h.spec positive lanePositive k hk

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitBlockCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitCallCT`. -/
section
/-! # Initialization's H′ calls leak only their public argument registers -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)

theorem hPrime_call_rel (v : HPrime.Backend) (name : String)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → VG.Proof.Argon2.AArch64.MemoryInit.CallReady s ∧ VG.Proof.Argon2.AArch64.MemoryInit.CallReady t ∧
      s.gpr .x1 = 72 ∧ t.gpr .x1 = 72 ∧ s.gpr .x3 = 1024 ∧ t.gpr .x3 = 1024 ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x2 = t.gpr .x2 ∧
      s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp) :
    RelCT isa P (.call name (VG.Impl.Argon2.AArch64.HPrime.code v.hash)) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := VG.Proof.Argon2.AArch64.MemoryInit.hPrime_call_hyps s hs ls os
  obtain ⟨pt, ct, wt⟩ := VG.Proof.Argon2.AArch64.MemoryInit.hPrime_call_hyps t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧
    s.callEntry.gpr .x4 = t.callEntry.gpr .x4 ∧
    s.callEntry.sp = t.callEntry.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, sp⟩

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Public registers survive each initialization H′ call -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

def savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

def AgreeSaved (s t : State) : Prop := HPrime.AgreeRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs s t

theorem blockArgs_rel (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved (.block (blockArgs column)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs)
    (fun _ _ h => h.taint) check

theorem block_rel (v : HPrime.Backend) (name : String) (column : Nat) (columnBound : column < 65536)
    (ct : ∃ hint, (taint.check (Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.AArch64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t)
      (VG.Impl.Argon2.AArch64.MemoryInit.block name v.hash column) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved := by
  let P := fun s t => VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.AArch64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t
  have args := ((VG.Proof.Argon2.AArch64.MemoryInit.blockArgs_rel column ct).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp => by
      exact ⟨VG.Proof.Argon2.AArch64.MemoryInit.blockArgs_ok s column columnBound (hp.1.prefix 64 (by decide)) (hp.1.prefix 68 (by decide)),
        VG.Proof.Argon2.AArch64.MemoryInit.blockArgs_ok t column columnBound (hp.2.1.prefix 64 (by decide)) (hp.2.1.prefix 68 (by decide))⟩)
  have call := VG.Proof.Argon2.AArch64.MemoryInit.hPrime_call_rel v name (P := fun a b =>
      True ∧ ∃ s t, P s t ∧ VG.Proof.Argon2.AArch64.MemoryInit.BlockArgs s a column ∧ VG.Proof.Argon2.AArch64.MemoryInit.BlockArgs t b column) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.ready hp.1, hb.ready hp.2.1, ha.inputLength, hb.inputLength,
      ha.outputLength, hb.outputLength, ?_, ?_, ?_, ?_⟩
    · exact ha.input.trans ((hp.2.2.2 .x19 (by decide)).trans hb.input.symm)
    · exact ha.output.trans ((hp.2.2.2 .x22 (by decide)).trans hb.output.symm)
    · exact ha.work.trans ((hp.2.2.2 .x24 (by decide)).trans hb.work.symm)
    · exact ha.sp.trans (hp.2.2.1.trans hb.sp.symm))
  have full := (args.seq call).wpDep (fun s t hp =>
    ⟨VG.Proof.Argon2.AArch64.MemoryInit.block_ok v name s column columnBound hp.1, VG.Proof.Argon2.AArch64.MemoryInit.block_ok v name t column columnBound hp.2.1⟩)
  exact full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.sp.trans (hp.2.2.1.trans hb.sp.symm), ?_⟩
    intro r hr
    have saved : ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.savedRegs, r ∈ FillCompress.loopRegs := by decide
    exact (ha.regs r (saved r hr)).trans ((hp.2.2.2 r hr).trans (hb.regs r (saved r hr)).symm))

theorem blocks_rel (v : HPrime.Backend) (name : String) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.AArch64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t)
      (VG.Impl.Argon2.AArch64.MemoryInit.block name v.hash 0) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved ∧
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.MemoryInit.BlockReady s ∧ VG.Proof.Argon2.AArch64.MemoryInit.BlockReady t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t)
      (VG.Impl.Argon2.AArch64.MemoryInit.block name v.hash 1) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved :=
  ⟨VG.Proof.Argon2.AArch64.MemoryInit.block_rel v name 0 (by decide) ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.AArch64.MemoryInit.block_rel v name 1 (by decide) ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitLoopCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitLaneCT`. -/
section
/-! # The two leading blocks of a lane have a public execution trace -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

structure LaneReady (memory : Addr) (bytes d : Nat) (s : State) : Prop where
  space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory bytes
  destination : s.gpr .x22 = memory + BitVec.ofNat 64 d

def RelatedLane (memory : Addr) (bytes d : Nat) (s t : State) : Prop :=
  VG.Proof.Argon2.AArch64.MemoryInit.LaneReady memory bytes d s ∧ VG.Proof.Argon2.AArch64.MemoryInit.LaneReady memory bytes d t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t

theorem BlockDone.laneReady {s t : State} {column : Nat} {memory : Addr} {bytes d : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.BlockDone s t column) (ready : VG.Proof.Argon2.AArch64.MemoryInit.LaneReady memory bytes d s) :
    VG.Proof.Argon2.AArch64.MemoryInit.LaneReady memory bytes d t :=
  ⟨ready.space.same h.wr (h.regs .x19 (by decide)) (h.regs .x24 (by decide))
    h.sp, (h.regs .x22 (by decide)).trans ready.destination⟩

theorem block_lane_rel (v : HPrime.Backend) (name : String) (column : Nat) (columnBound : column < 65536)
    (ct : ∃ hint, (taint.check (Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs)
      (.block (blockArgs column)) hint).isSome = true)
    (memory : Addr) (bytes d : Nat) (bound : d + 1024 ≤ bytes) :
    RelCT isa (VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes d) (VG.Impl.Argon2.AArch64.MemoryInit.block name v.hash column)
      (VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes d) := by
  have h := ((VG.Proof.Argon2.AArch64.MemoryInit.block_rel v name column columnBound ct).mono
    (P' := VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes d) (fun _ _ hp =>
      ⟨hp.1.space.blockReady hp.1.destination bound,
        hp.2.1.space.blockReady hp.2.1.destination bound, hp.2.2⟩)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨VG.Proof.Argon2.AArch64.MemoryInit.block_ok v name s column columnBound (hp.1.space.blockReady hp.1.destination bound),
        VG.Proof.Argon2.AArch64.MemoryInit.block_ok v name t column columnBound (hp.2.1.space.blockReady hp.2.1.destination bound)⟩)
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ha.laneReady hp.1, hb.laneReady hp.2.1, pub⟩)

theorem advance_rel : RelCT isa VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved
    (.block ([Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten)) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs)
    (fun _ _ h => h.taint) VG.Proof.Argon2.AArch64.MemoryInit.savedRegs
  taint_decide

theorem advance_lane_rel (memory : Addr) (bytes d : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes d) (.block ([Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten))
      (VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes (d + 1024)) := by
  have h := (advance_rel.mono (P' := VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes d)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.AArch64.MemoryInit.advance_ok s, VG.Proof.Argon2.AArch64.MemoryInit.advance_ok t⟩)
  have ready {s t : State} (h : VG.Proof.Argon2.AArch64.MemoryInit.Advanced s t) (hs : VG.Proof.Argon2.AArch64.MemoryInit.LaneReady memory bytes d s) :
      VG.Proof.Argon2.AArch64.MemoryInit.LaneReady memory bytes (d + 1024) t := by
    refine ⟨hs.space.same h.wr (h.other .x19 (by decide) (by decide) (by decide))
      (h.other .x24 (by decide) (by decide) (by decide)) h.sp, ?_⟩
    rw [h.destination, hs.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ready ha hp.1, ready hb hp.2.1, pub⟩)

theorem laneEnd_rel : RelCT isa VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved
    (.block ([Impl.Argon2.AArch64.Instructions.add .x22 .x21, Impl.Argon2.AArch64.Instructions.subi .x22 1024,
      Impl.Argon2.AArch64.Instructions.addi .x20 1, Impl.Argon2.AArch64.Instructions.subi .x23 1].flatten)) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.savedRegs)
    (fun _ _ h => h.taint) VG.Proof.Argon2.AArch64.MemoryInit.savedRegs
  taint_decide

theorem lane_rel (v : HPrime.Backend) (name : String)
    (memory : Addr) (bytes d : Nat) (bound : d + 2048 ≤ bytes) :
    RelCT isa (VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory bytes d) (lane name v.hash) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved := by
  exact (VG.Proof.Argon2.AArch64.MemoryInit.block_lane_rel v name 0 (by decide) ⟨_, by taint_decide⟩ memory bytes d (by omega)).seq
    ((VG.Proof.Argon2.AArch64.MemoryInit.advance_lane_rel memory bytes d).seq
    ((VG.Proof.Argon2.AArch64.MemoryInit.block_lane_rel v name 1 (by decide) ⟨_, by taint_decide⟩ memory bytes (d + 1024) (by omega)).seq
      (laneEnd_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h))))

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Both initialization loops count only pubNext matrix dimensions -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

theorem lanesLoop_rel (v : HPrime.Backend) (name : String)
    (s₁ s₂ : State) (memory : Addr) (lanes q : Nat) (h₁ h₂ : List Byte)
    (space₁ : VG.Proof.Argon2.AArch64.MemoryInit.Space s₁ memory (1024 * (lanes * q)))
    (space₂ : VG.Proof.Argon2.AArch64.MemoryInit.Space s₂ memory (1024 * (lanes * q)))
    (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₁ memory lanes q 0 h₁ s ∧
      VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₂ memory lanes q 0 h₂ t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t)
      (.loop (lane name v.hash) (.nonzero .x .x15)) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved := by
  let I := fun n s t => ∃ j, n = lanes - j ∧ j < lanes ∧
    VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₁ memory lanes q j h₁ s ∧ VG.Proof.Argon2.AArch64.MemoryInit.LoopI s₂ memory lanes q j h₂ t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t
  have steps : ∀ n, RelCT isa (I n) (lane name v.hash) fun a b =>
      isa.eval (.nonzero .x .x15) a = isa.eval (.nonzero .x .x15) b ∧
      (isa.eval (.nonzero .x .x15) a = some false → VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved a b) ∧
      (isa.eval (.nonzero .x .x15) a = some true → ∃ m < n, I m a b) := by
    intro n s t trace₁ trace₂ a b hp e₁ e₂
    obtain ⟨j, rfl, hj, hs, ht, pub⟩ := hp
    have bound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
      have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    have related : VG.Proof.Argon2.AArch64.MemoryInit.RelatedLane memory (1024 * (lanes * q)) (1024 * (j * q)) s t :=
      ⟨⟨space₁.keeps hs.keeps, hs.destination⟩,
        ⟨space₂.keeps ht.keeps, ht.destination⟩, pub⟩
    obtain ⟨trace, pubNext⟩ := VG.Proof.Argon2.AArch64.MemoryInit.lane_rel v name memory _ _ bound _ _ _ _ _ _ related e₁ e₂
    obtain ⟨_, a', ea, ha⟩ := VG.Proof.Argon2.AArch64.MemoryInit.lane_step v name s₁ s memory lanes q j h₁
      space₁ hj lanesBound hq hs
    obtain ⟨_, b', eb, hb⟩ := VG.Proof.Argon2.AArch64.MemoryInit.lane_step v name s₂ t memory lanes q j h₂
      space₂ hj lanesBound hq ht
    obtain ⟨-, rfl⟩ := Exec.det e₁ ea
    obtain ⟨-, rfl⟩ := Exec.det e₂ eb
    refine ⟨trace, ?_, fun _ => pubNext, ?_⟩
    · simp only [ha.2, hb.2]
    · intro taken
      have remaining : lanes - (j + 1) ≠ 0 := by
        intro zero
        have flag := ha.2
        change eval (.nonzero .x .x15) a = some true at taken
        rw [taken] at flag
        simp only [zero, ne_eq, not_true_eq_false, decide_false, Option.some.injEq, Bool.true_eq_false] at flag
      exact ⟨lanes - (j + 1), by omega, j + 1, rfl, by omega, ha.1, hb.1, pubNext⟩
  exact (RelCT.loop I steps lanes).mono (fun _ _ hp =>
    ⟨0, by omega, lo, hp.1, hp.2.1, hp.2.2⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitDone`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitClearCT`. -/
section
/-! # Matrix clearing uses only public addresses and the public allocation size -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure Ready (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory (1024 * (lanes * q))
  memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8
  lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8
  blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8
  memoryWord : VG.Proof.Argon2.AArch64.Initial.wordAt s memoryOffset = memory
  lanesWord : VG.Proof.Argon2.AArch64.Initial.wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes
  blocksWord : VG.Proof.Argon2.AArch64.Initial.wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q)
  laneLength : s.gpr .x21 = BitVec.ofNat 64 q

def publicBases : List Reg := [.x19, .x24, .x21]

def AgreeBases (s t : State) : Prop := HPrime.AgreeRegs VG.Proof.Argon2.AArch64.MemoryInit.publicBases s t

theorem clearSetup_rel : RelCT isa VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases clearSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.publicBases)
    (fun _ _ h => h.taint) (by taint_decide)

theorem clearLoop_rel : RelCT isa
    (fun s t => VG.AArch64.Taint.Agree (Taint.ofRegs (.x8 :: .x22 :: VG.Proof.Argon2.AArch64.MemoryInit.publicBases)) s t)
    (.loop (.block clearWord) (.nonzero .x .x15)) VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases := by
  apply RelCT.taintRegs (τ := Taint.ofRegs (.x8 :: .x22 :: VG.Proof.Argon2.AArch64.MemoryInit.publicBases))
    (fun _ _ h => h) VG.Proof.Argon2.AArch64.MemoryInit.publicBases
  taint_decide

theorem clear_rel (memory : Addr) (lanes q : Nat) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q s ∧ VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases s t)
      clear VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases := by
  let P := fun s t => VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q s ∧ VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases s t
  have prep := (clearSetup_rel.mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨VG.Proof.Argon2.AArch64.MemoryInit.clearSetup_ok s h.1.memoryRead h.1.blocksRead,
        VG.Proof.Argon2.AArch64.MemoryInit.clearSetup_ok t h.2.1.memoryRead h.2.1.blocksRead⟩)
  refine prep.seq (clearLoop_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.sp.trans (hp.2.2.1.trans hb.sp.symm), ?_⟩
  intro r hr
  have hr := RegSet.mem_ofList.mp hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rw [ha.count, hb.count, hp.1.blocksWord, hp.2.1.blocksWord]
  · rw [ha.destination, hb.destination, hp.1.memoryWord, hp.2.1.memoryWord]
  · have excluded : ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.publicBases, r ≠ .x22 ∧ r ≠ .x8 ∧ r ≠ .x3 ∧ r ≠ .x12 ∧ r ≠ .x15 := by decide
    have hn := excluded r hr
    exact (ha.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((hp.2.2.2 r hr).trans (hb.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).symm)

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitCT`. -/
section
/-! # The complete memory initialization trace depends only on public parameters -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopReady (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory (1024 * (lanes * q))
  initialized : VG.Proof.Argon2.AArch64.MemoryInit.Initialized s.mem memory lanes q 0 (bytesAt s.mem (s.gpr .x19) 64)
  destination : s.gpr .x22 = memory
  lane : s.gpr .x20 = 0
  remaining : s.gpr .x23 = BitVec.ofNat 64 lanes
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * q)

theorem Cleared.ready {s t : State} {memory : Addr} {lanes q : Nat}
    (h : VG.Proof.Argon2.AArch64.MemoryInit.Cleared s t memory (lanes * q)) (hs : VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q s) :
    VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q t := by
  have bp := h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bx := h.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp := h.sp
  refine ⟨hs.space.same h.wr bp bx sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.rd, h.wr, bp]; exact hs.memoryRead
  · rw [h.rd, h.wr, bp]; exact hs.lanesRead
  · rw [h.rd, h.wr, bp]; exact hs.blocksRead
  · exact (h.word hs.space (by decide)).trans hs.memoryWord
  · exact (h.word hs.space (by decide)).trans hs.lanesWord
  · exact (h.word hs.space (by decide)).trans hs.blocksWord
  · exact (h.other .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.laneLength

theorem Setup.loopReady {s a b : State} {memory : Addr} {lanes q : Nat}
    (hs : VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q s) (ha : VG.Proof.Argon2.AArch64.MemoryInit.Cleared s a memory (lanes * q))
    (hb : VG.Proof.Argon2.AArch64.MemoryInit.Setup a b memory lanes q) : VG.Proof.Argon2.AArch64.MemoryInit.LoopReady memory lanes q b := by
  have ready := ha.ready hs
  refine ⟨ready.space.same hb.wr (hb.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.sp, ?_,
    hb.destination, hb.lane, hb.remaining, hb.stride⟩
  rw [hb.mem, ha.mem]
  exact VG.Proof.Argon2.AArch64.MemoryInit.initialized_zero s.mem memory lanes q hs.space.bound _

theorem lanesSetup_rel : RelCT isa VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases lanesSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Argon2.AArch64.MemoryInit.publicBases)
    (fun _ _ h => h.taint) (by taint_decide)

theorem Setup.agree {s t a b : State} {memory : Addr} {lanes q : Nat}
    (ha : VG.Proof.Argon2.AArch64.MemoryInit.Setup s a memory lanes q) (hb : VG.Proof.Argon2.AArch64.MemoryInit.Setup t b memory lanes q)
    (hp : VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases s t) : VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved a b := by
  refine ⟨ha.sp.trans (hp.1.trans hb.sp.symm), ?_⟩
  intro r hr
  by_cases h14 : r = .x22
  · subst r; exact ha.destination.trans hb.destination.symm
  by_cases h12 : r = .x20
  · subst r; exact ha.lane.trans hb.lane.symm
  by_cases h15 : r = .x23
  · subst r; exact ha.remaining.trans hb.remaining.symm
  by_cases h13 : r = .x21
  · subst r; exact ha.stride.trans hb.stride.symm
  have included : ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.savedRegs, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x21 →
      r ∈ VG.Proof.Argon2.AArch64.MemoryInit.publicBases := by decide
  exact (ha.other r h14 h12 h15 h13 ((show ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.savedRegs, r ≠ .x15 from by decide) r hr)).trans
    ((hp.2 r (included r hr h14 h12 h15 h13)).trans (hb.other r h14 h12 h15 h13 ((show ∀ r ∈ VG.Proof.Argon2.AArch64.MemoryInit.savedRegs, r ≠ .x15 from by decide) r hr)).symm)

theorem lanesLoop_ready_rel (v : HPrime.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.MemoryInit.LoopReady memory lanes q s ∧ VG.Proof.Argon2.AArch64.MemoryInit.LoopReady memory lanes q t ∧
      VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved s t) (.loop (lane name v.hash) (.nonzero .x .x15)) VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved := by
  intro s t ts tt a b hp es et
  have initial {s : State} (h : VG.Proof.Argon2.AArch64.MemoryInit.LoopReady memory lanes q s) :
      VG.Proof.Argon2.AArch64.MemoryInit.LoopI s memory lanes q 0 (bytesAt s.mem (s.gpr .x19) 64) s :=
    ⟨by omega, by simpa using h.destination, h.lane,
      by simpa only [Nat.sub_zero] using h.remaining, h.stride, Keeps.refl _ _ _,
      h.initialized, rfl⟩
  exact VG.Proof.Argon2.AArch64.MemoryInit.lanesLoop_rel v name s t memory lanes q _ _ hp.1.space hp.2.1.space lo
    lanesBound hq _ _ _ _ _ _ ⟨initial hp.1, initial hp.2.1, hp.2.2⟩ es et

theorem code_ct (v : HPrime.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    ConstantTime isa (VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q) VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases (VG.Impl.Argon2.AArch64.MemoryInit.code name v.hash) := by
  let P := fun s t => VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q s ∧ VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q t ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases s t
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  have cleared := (VG.Proof.Argon2.AArch64.MemoryInit.clear_rel memory lanes q).wpDep (fun s t hp =>
    ⟨VG.Proof.Argon2.AArch64.MemoryInit.clear_ok s memory (lanes * q) blocksPositive hp.1.space.bound hp.1.memoryRead
        hp.1.blocksRead hp.1.memoryWord hp.1.blocksWord hp.1.space.matrix,
      VG.Proof.Argon2.AArch64.MemoryInit.clear_ok t memory (lanes * q) blocksPositive hp.2.1.space.bound hp.2.1.memoryRead
        hp.2.1.blocksRead hp.2.1.memoryWord hp.2.1.blocksWord hp.2.1.space.matrix⟩)
  let R := fun a b => VG.Proof.Argon2.AArch64.MemoryInit.AgreeBases a b ∧ ∃ s t, P s t ∧
    VG.Proof.Argon2.AArch64.MemoryInit.Cleared s a memory (lanes * q) ∧ VG.Proof.Argon2.AArch64.MemoryInit.Cleared t b memory (lanes * q)
  have setup := (lanesSetup_rel.mono (P' := R) (fun _ _ h => h.1)
    (fun _ _ h => h)).wpDep (F := fun a b => VG.Proof.Argon2.AArch64.MemoryInit.Setup a b memory lanes q) (by
    intro a b hp
    obtain ⟨_, s, t, hst, ha, hb⟩ := hp
    have ra := ha.ready hst.1
    have rb := hb.ready hst.2.1
    exact ⟨VG.Proof.Argon2.AArch64.MemoryInit.lanesSetup_ok a memory lanes q ra.memoryRead ra.lanesRead ra.memoryWord
        ra.lanesWord ra.laneLength,
      VG.Proof.Argon2.AArch64.MemoryInit.lanesSetup_ok b memory lanes q rb.memoryRead rb.lanesRead rb.memoryWord
        rb.lanesWord rb.laneLength⟩)
  have prepared : RelCT isa R lanesSetupCode (fun a b =>
      VG.Proof.Argon2.AArch64.MemoryInit.LoopReady memory lanes q a ∧ VG.Proof.Argon2.AArch64.MemoryInit.LoopReady memory lanes q b ∧ VG.Proof.Argon2.AArch64.MemoryInit.AgreeSaved a b) := setup.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, c, d, hp, ha, hb⟩ := h
    obtain ⟨pub, s, t, hst, hc, hd⟩ := hp
    exact ⟨ha.loopReady hst.1 hc, hb.loopReady hst.2.1 hd, ha.agree hb pub⟩)
  exact (cleared.seq (prepared.seq (VG.Proof.Argon2.AArch64.MemoryInit.lanesLoop_ready_rel v name memory lanes q lo
    lanesBound hq))).constantTime

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Initialization retains its byte stride and every public frame word outside its lane suffix. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  initialized : VG.Proof.Argon2.AArch64.MemoryInit.Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .x19) 64)
  bp : t.gpr .x19 = s.gpr .x19
  bx : t.gpr .x24 = s.gpr .x24
  sp : t.sp = s.sp
  stride : t.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem complete_ok (v : HPrime.Backend) (name : String) (s : State)
    (memory : Addr) (lanes q : Nat) (ready : VG.Proof.Argon2.AArch64.MemoryInit.Ready memory lanes q s)
    (positive : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (minimum : 2 ≤ q) :
    WP isa (Impl.Argon2.AArch64.MemoryInit.code name v.hash) s (VG.Proof.Argon2.AArch64.MemoryInit.Done s · memory lanes q) :=
  (VG.Proof.Argon2.AArch64.MemoryInit.code_ok v name s memory lanes q positive minimum lanesBound ready.space ready.memoryRead ready.lanesRead
    ready.blocksRead ready.memoryWord ready.lanesWord ready.blocksWord ready.laneLength).mono
      (fun _ ⟨initialized, bp, bx, sp, stride, rd, wr, frame, unused⟩ =>
        ⟨initialized, bp, bx, sp, stride, rd, wr, frame, unused⟩)

theorem Done.frame_word {s t : State} {memory : Addr} {lanes q : Nat}
    (space : VG.Proof.Argon2.AArch64.MemoryInit.Space s memory (1024 * (lanes * q))) (done : VG.Proof.Argon2.AArch64.MemoryInit.Done s t memory lanes q)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 64 ∨ 72 ≤ d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [done.bp]
  have sub : Region.Sub ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact space.frameMatrix.sub_left sub
    · exact space.frameWork.sub_left sub
    · exact space.stackFrame.symm.sub_left sub
    · exact Offset.disjoint (s.gpr .x19) separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.InitFillReady`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSetupReset`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSetupDimensions`. -/
section
/-! Initialization's byte stride gives exact block and segment counts without division instructions. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

theorem dimensions_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.FillSetup.dimensions) s fun t =>
    t.gpr .x20 = s.gpr .x21 >>> 10 ∧ t.gpr .x21 = s.gpr .x21 >>> 12 ∧ Divide.Keeps [.x20, .x21, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.FillSetup.dimensions,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.shr,
    Impl.Argon2.AArch64.Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, show (10 : Nat) < 64 from by decide,
    show (12 : Nat) < 64 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem stride_shift (q shift : Nat) (bound : 1024 * q < 2 ^ 64) :
    BitVec.ofNat 64 (1024 * q) >>> shift = BitVec.ofNat 64 ((1024 * q) / 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) bound)]

theorem dimensions_nat_ok (s : State) (p : Params) (bound : 1024 * p.laneLen < 2 ^ 64)
    (stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * p.laneLen)) :
    WP isa (.block Impl.Argon2.AArch64.FillSetup.dimensions) s fun t =>
      t.gpr .x20 = BitVec.ofNat 64 p.laneLen ∧ t.gpr .x21 = BitVec.ofNat 64 p.segmentLen ∧
      Divide.Keeps [.x20, .x21, .x15] s t := by
  refine (VG.Proof.Argon2.AArch64.FillSetup.dimensions_ok s).mono ?_
  rintro t ⟨lane, segment, keeps⟩
  refine ⟨?_, ?_, keeps⟩
  · rw [lane, stride, VG.Proof.Argon2.AArch64.FillSetup.stride_shift _ 10 bound]
    simp only [show 2 ^ 10 = 1024 from rfl, Nat.mul_div_cancel_left _ (by decide : 0 < 1024)]
  · rw [segment, stride, VG.Proof.Argon2.AArch64.FillSetup.stride_shift _ 12 bound]
    have div : 1024 * p.laneLen / 4096 = p.laneLen / 4 := by
      rw [show (4096 : Nat) = 1024 * 4 from rfl, Nat.mul_div_mul_left _ _ (by decide : 0 < 1024)]
    rw [show 2 ^ 12 = 4096 from rfl, div]
    rfl

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Reset public loop coordinates and only the pass word in the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Reset (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (0 : Addr)
  lane : t.gpr .x24 = 0
  slice : t.gpr .x22 = 0
  regs : ∀ r, r ∉ [Reg.x8, .x24, .x22] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem reset_ok (s : State) (write : InRegions s.wr (off (s.gpr .x19) 0) 8) :
    WP isa (.block Impl.Argon2.AArch64.FillSetup.reset) s (VG.Proof.Argon2.AArch64.FillSetup.Reset s) := by
  apply WP.of_runBlock
  simp only [off, BitVec.add_zero] at write
  simp only [Impl.Argon2.AArch64.FillSetup.reset,
    Impl.Argon2.AArch64.Instructions.imm, Impl.Argon2.AArch64.Instructions.store,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, Size.bits, State.store, State.read,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (0#16).setWidth 64 = 0#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.add_zero, BitVec.setWidth_eq, write, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.mem_write, off, BitVec.add_zero, Mem.writeW]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem Reset.pass {s t : State} (h : VG.Proof.Argon2.AArch64.FillSetup.Reset s t) : t.mem.readW (off (t.gpr .x19) 0) 64 = 0 := by
  rw [h.mem, h.regs .x19 (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem Reset.frame {s t : State} (h : VG.Proof.Argon2.AArch64.FillSetup.Reset s t) : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (r := ⟨s.gpr .x19, 8⟩) (by simp) _
    (by simpa only [off, BitVec.add_zero] using Region.contains_self (s.gpr .x19) 8)

theorem Reset.read {s t : State} (h : VG.Proof.Argon2.AArch64.FillSetup.Reset s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.mem, h.regs .x19 (by decide)]
  exact Mem.readW_writeW_sep (w := 64) (w' := 64)
    (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Merged from `Proof.Argon2.AArch64.FillSetupFinish`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSetupEnvironment`. -/
section
/-! Initialization hands filling the reviewed dimensions and stable public frame words. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Environment (p : Params) (s : State) : Prop where
  parameters : FillContext.Parameters p 0 0 0
  passesBound : p.passes < 2 ^ 32
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  counterWrite : InRegions s.wr (off (s.gpr .x19) 8) 8
  passWrite : InRegions s.wr (off (s.gpr .x19) 0) 8
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  blocksWord : s.mem.readW (off (s.gpr .x19) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .x19) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Environment.of_state {p : Params} {s t : State} (h : VG.Proof.Argon2.AArch64.FillSetup.Environment p s)
    (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.AArch64.FillSetup.Environment p t := by
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

theorem Reset.header {p : Params} {s t : State} (h : VG.Proof.Argon2.AArch64.FillSetup.Environment p s) (reset : VG.Proof.Argon2.AArch64.FillSetup.Reset s t)
    (laneLength : t.gpr .x20 = BitVec.ofNat 64 p.laneLen)
    (segmentLength : t.gpr .x21 = BitVec.ofNat 64 p.segmentLen) : FillHeader.Ready p 0 0 0 t := by
  have bp := reset.regs .x19 (by decide)
  have sp := reset.sp
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
  · refine ⟨(s.mem.readW (off (s.gpr .x19) 8) 64).toNat, reset.pass, reset.lane, reset.slice,
      (reset.read 240 (by decide) (by decide)).trans h.blocksWord,
      (reset.read 72 (by decide) (by decide)).trans h.passesWord,
      (reset.read 112 (by decide) (by decide)).trans h.variantWord, ?_⟩
    rw [reset.read 8 (by decide) (by decide)]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Merged from `Proof.Argon2.AArch64.FillSetup`. -/
section
/-! Establish the complete pass-loop invariant from memory initialization's byte stride. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  environment : VG.Proof.Argon2.AArch64.FillSetup.Environment p s
  bound : 1024 * p.laneLen < 2 ^ 64
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * p.laneLen)

structure Prepared (s t : State) (p : Params) : Prop where
  ready : FillIterations.Ready p 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem
  sp : t.sp = s.sp
  words : ∀ d, 8 ≤ d → d + 8 ≤ 272 →
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64

theorem code_ok (s : State) (p : Params) (h : VG.Proof.Argon2.AArch64.FillSetup.Ready p s) :
    WP isa Impl.Argon2.AArch64.FillSetup.code s (VG.Proof.Argon2.AArch64.FillSetup.Prepared s · p) := by
  unfold Impl.Argon2.AArch64.FillSetup.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.FillSetup.dimensions_nat_ok s p h.bound h.stride).mono ?_)
  rintro a ⟨laneLength, segmentLength, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have environment := h.environment.of_state bp sp keeps.mem keeps.rd keeps.wr
  refine (VG.Proof.Argon2.AArch64.FillSetup.reset_ok a environment.passWrite).mono ?_
  intro t reset
  have header := reset.header environment ((reset.regs .x20 (by decide)).trans laneLength)
    ((reset.regs .x21 (by decide)).trans segmentLength)
  have words (d : Nat) (lower : 8 ≤ d) (upper : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [reset.read d lower upper, keeps.mem, bp]
  refine ⟨⟨⟨environment.parameters, 0, 0, header⟩, environment.passesBound, ?_⟩,
    words 232 (by decide) (by decide), words 248 (by decide) (by decide), ?_,
    reset.rd.trans keeps.rd, reset.wr.trans keeps.wr, ?_, reset.sp.trans keeps.sp, words⟩
  · rw [reset.wr, reset.regs .x19 (by decide)]; exact environment.passWrite
  · intro r hr bx q g sl
    have ne : r ≠ .x8 ∧ r ≠ .x15 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reset.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ne.1, bx, sl⟩)).trans
      (keeps.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨q, g, ne.2⟩))
  · have frame := reset.frame
    rw [bp, keeps.mem] at frame; exact frame

theorem Prepared.represents {s t : State} {p : Params} (ready : VG.Proof.Argon2.AArch64.FillSetup.Ready p s) (done : VG.Proof.Argon2.AArch64.FillSetup.Prepared s t p)
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

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.FillSetup.code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Filling setup retains the final-call layout and establishes the reduction dimensions. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

theorem Prepared.finish_ready {s t : State} {p : Params} (ready : VG.Proof.Argon2.AArch64.FillSetup.Ready p s) (done : VG.Proof.Argon2.AArch64.FillSetup.Prepared s t p)
    (outputReady : FinalOutput.Ready p s) (positive : 0 < p.passes) : FillFinish.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)
  have sp := done.sp
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
  · refine ⟨?_, outputReady.positive, outputReady.bound, ?_,
      (done.words 264 (by decide) (by decide)).trans outputReady.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sp]; exact outputReady.stackMinimum
    · rw [done.rd, done.wr, bp]; exact outputReady.reads
    · rw [base, done.rd, done.wr]; exact outputReady.input
    · rw [output, done.wr]; exact outputReady.outputWrite
    · rw [work, done.wr]; exact outputReady.workWrite
    · rw [base, work]; exact outputReady.inputWork
    · rw [output, work]; exact outputReady.outputWork
    · rw [sp, base]; exact outputReady.stackInput
    · rw [sp, output]; exact outputReady.stackOutput
    · rw [sp, work]; exact outputReady.stackWork

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Retain the filling environment and final-call layout across memory initialization. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  initializing : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen s
  environment : FillSetup.Environment p s
  output : FinalOutput.Ready p s
  positive : 0 < p.passes
  scratch : s.gpr .x24 = FinalOutput.work s

theorem initialized_environment {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.InitFill.Ready p s)
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

theorem initialized_output {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  refine ⟨(by rw [done.sp]; exact h.output.stackMinimum), h.output.positive, h.output.bound, ?_,
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

theorem initialized_setup {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Ready p t := by
  have params := h.environment.parameters
  have product : p.laneLen ≤ p.lanes * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ p.lanes from params.lanesPositive)
  refine ⟨VG.Proof.Argon2.AArch64.InitFill.initialized_environment h done, ?_, done.stride⟩
  have bound := h.initializing.space.bound
  have bytes := Nat.mul_le_mul_left 1024 product
  omega

theorem initialized_represents {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
      (initMemory p (Spec.Blake2.bytesAt s.mem (s.gpr .x19) 64)).memory := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  rw [base]
  have segments := Proof.Argon2.laneLen_segments p h.environment.parameters.lanesPositive
  have minimum := h.environment.parameters.segment_bound.1
  exact done.initialized.represents h.environment.parameters.lanesPositive (by omega)

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Merged from `Proof.Argon2.AArch64.InitFillFrames`. -/
section
/-! Each stage writes only the matrix, hash scratch, output, call stack and local hash prefix. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨FinalOutput.work s, 16384⟩,
    ⟨FinalOutput.output s, p.tagLen⟩, below (s.sp) 16, ⟨s.gpr .x19, 72⟩]

theorem initialization_frame {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.InitFill.Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : Frame (VG.Proof.Argon2.AArch64.InitFill.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have blocks := Proof.Argon2.blocks_lanes p h.environment.parameters.lanesPositive
    exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], by rw [blocks, Nat.mul_comm 1024]; intro _ h; exact h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], by rw [h.scratch]; intro _ h; exact h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x19, 72⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], Offset.sub_base _ (by decide)⟩

theorem setup_frame {s t : State} {p : Params} (h : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem) :
    Frame (VG.Proof.Argon2.AArch64.InitFill.writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .x19, 72⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], Region.sub_prefix (by decide)⟩

theorem filling_frame {s t : State} {p : Params} (positive : 0 < p.blocks) (h : Frame (FillFinish.writes s p) s.mem t.mem) :
    Frame (VG.Proof.Argon2.AArch64.InitFill.writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillFinish.writes, FillIterations.writes, Finish.writes,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], fun _ h => h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.sp) 16, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .x19, 72⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], Region.sub_prefix (by omega)⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.AArch64.InitFill.writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Exact initialization, every filling pass, final reduction and H′ after the reviewed H₀. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def result (p : Params) (h0 : List Byte) : List Byte :=
  Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes (initMemory p h0)).memory

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = VG.Proof.Argon2.AArch64.InitFill.result p (bytesAt s.mem (s.gpr .x19) 64)
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.AArch64.InitFill.writes s p) s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem writes_eq (s t : State) (p : Params) (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : FillKernel.matrix t = FillKernel.matrix s) (work : FinalOutput.work t = FinalOutput.work s)
    (output : FinalOutput.output t = FinalOutput.output s) : VG.Proof.Argon2.AArch64.InitFill.writes t p = VG.Proof.Argon2.AArch64.InitFill.writes s p := by
  unfold VG.Proof.Argon2.AArch64.InitFill.writes
  rw [bp, sp, base, work, output]

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params) (h : VG.Proof.Argon2.AArch64.InitFill.Ready p s) :
    WP isa (Impl.Argon2.AArch64.InitFill.code name v.hash) s (VG.Proof.Argon2.AArch64.InitFill.Done s · p) := by
  have params := h.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have blocks := Proof.Argon2.lastIndex_bounds p params.lanesPositive params.segment_bound.1 0 params.lanesPositive
  unfold Impl.Argon2.AArch64.InitFill.code
  refine WP.seq ((MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen h.initializing
    params.lanesPositive (Nat.lt_trans params.lanesBound (by decide)) q).mono ?_)
  intro a initialized
  have setupReady := VG.Proof.Argon2.AArch64.InitFill.initialized_setup h initialized
  have initializedBase : FillKernel.matrix a = FillKernel.matrix s :=
    initialized.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have initializedWork : FinalOutput.work a = FinalOutput.work s :=
    initialized.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have initializedOutput : FinalOutput.output a = FinalOutput.output s :=
    initialized.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have rep : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks
      (initMemory p (bytesAt s.mem (s.gpr .x19) 64)).memory := by
    rw [initializedBase]
    exact initialized.initialized.represents params.lanesPositive (by omega)
  refine WP.seq ((FillSetup.code_ok a p setupReady).mono ?_)
  intro b prepared
  refine (FillFinish.code_ok v name b p (prepared.finish_ready setupReady (VG.Proof.Argon2.AArch64.InitFill.initialized_output h initialized) h.positive)
    (initMemory p (bytesAt s.mem (s.gpr .x19) 64)) (prepared.represents setupReady _ rep)).mono ?_
  intro t filled
  have bp := prepared.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)
  have sp := prepared.sp
  have work : FinalOutput.work b = FinalOutput.work a := prepared.words 248 (by decide) (by decide)
  have output : FinalOutput.output b = FinalOutput.output a := prepared.words 256 (by decide) (by decide)
  refine ⟨?_, (filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans (bp.trans initialized.bp),
    filled.sp.trans (sp.trans initialized.sp),
    filled.rd.trans (prepared.rd.trans initialized.rd), filled.wr.trans (prepared.wr.trans initialized.wr), ?_, ?_⟩
  · have digest := filled.digest
    rw [output, initializedOutput] at digest
    exact digest
  · have initialFrame := VG.Proof.Argon2.AArch64.InitFill.initialization_frame h initialized
    have setupFrame := VG.Proof.Argon2.AArch64.InitFill.setup_frame (p := p) prepared.frame
    rw [VG.Proof.Argon2.AArch64.InitFill.writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at setupFrame
    have fillFrame := VG.Proof.Argon2.AArch64.InitFill.filling_frame (by omega : 0 < p.blocks) filled.frame
    rw [VG.Proof.Argon2.AArch64.InitFill.writes_eq a b p bp sp prepared.matrix work output,
      VG.Proof.Argon2.AArch64.InitFill.writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at fillFrame
    exact (initialFrame.trans setupFrame).trans fillFrame
  · intro r hr
    have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
        r ∈ FillCompress.loopRegs ∧ r ≠ .x24 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x20 ∧ r ≠ .x21 := by decide
    obtain ⟨member, h24, h22, h23, h20, h21⟩ := facts r hr
    exact (filled.regs r member h24 h22 h23).trans
      ((prepared.regs r member h24 h20 h21 h22).trans (initialized.unused r hr))

theorem result_derive (p : Params) (password salt secret ad : List Byte) :
    VG.Proof.Argon2.AArch64.InitFill.result p (initialHash p password salt secret ad) = derive p password salt secret ad := by
  unfold VG.Proof.Argon2.AArch64.InitFill.result derive
  rw [Proof.Argon2.iterations_fill]

end VG.Proof.Argon2.AArch64.InitFill

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialStart`. -/
section

section

section

/-! # Writing and reading the six words of the H₀ header -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def headerValue (s : State) (j : Nat) : BitVec 32 :=
  if j = 4 then 0x13 else (VG.Proof.Argon2.AArch64.Initial.wordAt s (headerSource j)).setWidth 32

def headerMem (s : State) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (VG.Proof.Argon2.AArch64.Initial.headerMem s n).writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * n))
    (VG.Proof.Argon2.AArch64.Initial.headerValue s n)

theorem headerSource_slot (j : Nat) : headerSource j ∈ VG.Proof.Argon2.AArch64.Initial.slots := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerSource_bound (j : Nat) : headerSource j + 8 ≤ 272 := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerValue_keeps {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) (j : Nat) :
    VG.Proof.Argon2.AArch64.Initial.headerValue t j = VG.Proof.Argon2.AArch64.Initial.headerValue s j := by
  unfold VG.Proof.Argon2.AArch64.Initial.headerValue
  rw [h.word_keeps k _ (VG.Proof.Argon2.AArch64.Initial.headerSource_bound j)]

theorem headerMem_frame (s : State) (n : Nat) (hn : n ≤ 6) :
    Frame [⟨s.gpr .x24 + 768, 24⟩] s.mem (VG.Proof.Argon2.AArch64.Initial.headerMem s n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega) (by omega))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (VG.Proof.Argon2.AArch64.Initial.headerMem s n).readW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      VG.Proof.Argon2.AArch64.Initial.headerValue s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold VG.Proof.Argon2.AArch64.Initial.headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem headerMem_bytes (s : State) :
    bytesAt (VG.Proof.Argon2.AArch64.Initial.headerMem s 6) (s.gpr .x24 + 768) 24 =
      (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s j)) := by
  rw [show 24 = 32 / 8 * 6 from rfl, Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl)]
  rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.add_assoc,
    ← BitVec.ofNat_add, VG.Proof.Argon2.AArch64.Initial.headerMem_read s 6 j (by decide) (List.mem_range.mp hj)]

theorem headerSlot_ok (s : State) (j : Nat) (hj : j < 6) (h : VG.Proof.Argon2.AArch64.Initial.Space s) :
    WP isa (.block (headerSlot j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (VG.Proof.Argon2.AArch64.Initial.headerValue s j) ∧
      VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  have hw := h.write (768 + 4 * j) 4 (by omega)
  have finish (t : State) (hm : t.mem = s.mem.writeW
      (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (VG.Proof.Argon2.AArch64.Initial.headerValue s j))
      (regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r)
      (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) :
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (VG.Proof.Argon2.AArch64.Initial.headerValue s j) ∧
        VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
    refine ⟨hm, fun r hr _ _ => regs r ?_, sp, rd, wr, ?_⟩
    · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by omega) (by omega))
  unfold headerSlot
  split
  · next he =>
    subst j
    have hwLiteral : InRegions s.wr (s.gpr .x24 + 784#64) 4 := hw
    apply WP.of_runBlock
    simp only [Impl.Argon2.AArch64.Instructions.imm,
      Impl.Argon2.AArch64.Instructions.store32, show 19 < 65536 from by decide,
      List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr,
      Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, Nat.reduceMod,
      BitVec.shiftLeft_zero, show (19#16).setWidth 64 = 19#64 from rfl,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      hwLiteral, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, and_self,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, ?_⟩
    constructor
    · intro r hr _ _
      have hn : r ≠ .x8 := by
        simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [RegUpd.gpr_write, hn, ite_false]
    · simp only [RegUpd.sp_write]
    · rfl
    · rfl
    · change Frame [⟨s.gpr .x24, 832⟩, below s.sp 16] s.mem
        (s.mem.writeW (s.gpr .x24 + 784) (19#32))
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (d := 784) (n := 4) (by decide : 784 + 4 ≤ 832) (by decide))
  · next he =>
    have align : headerSource j % 8 = 0 := by
      unfold headerSource
      split <;> (try split) <;> (try split) <;> (try split) <;> decide
    refine (headerWord_ok s _ _ align (by have := VG.Proof.Argon2.AArch64.Initial.headerSource_bound j; omega)
      (by omega) (by omega) (h.readable _ (VG.Proof.Argon2.AArch64.Initial.headerSource_slot j)) hw).mono ?_
    rintro t ⟨hm, regs, rd, wr, sp⟩
    exact finish t (by simpa only [VG.Proof.Argon2.AArch64.Initial.headerValue, he, ite_false, VG.Proof.Argon2.AArch64.Initial.wordAt] using hm) regs rd wr sp

theorem headerWords_ok (s : State) (n : Nat) (hn : n ≤ 6) (h : VG.Proof.Argon2.AArch64.Initial.Space s) :
    WP isa (.block ((List.range n).flatMap headerSlot)) s fun t =>
      t.mem = VG.Proof.Argon2.AArch64.Initial.headerMem s n ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine (ih (by omega)).mono ?_
    rintro u ⟨hu, ku⟩
    refine (VG.Proof.Argon2.AArch64.Initial.headerSlot_ok u n (by omega) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.x24, VG.Proof.Argon2.AArch64.Initial.headerValue_keeps h ku, hu]
    rfl

theorem header_ok (s : State) (h : VG.Proof.Argon2.AArch64.Initial.Space s) :
    WP isa (.block VG.Impl.Argon2.AArch64.Initial.header) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 24 =
        (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s j)) ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t :=
  (VG.Proof.Argon2.AArch64.Initial.headerWords_ok s 6 (by decide) h).mono fun t ⟨hm, hk⟩ =>
    ⟨by rw [hm]; exact VG.Proof.Argon2.AArch64.Initial.headerMem_bytes s, hk⟩

end VG.Proof.Argon2.AArch64.Initial

end

/-! Merged from `Proof.Argon2.AArch64.InitialPrep`. -/
section
/-! # H₀: preserving the stack across input argument preparation -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

theorem LengthArgs.keeps {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  refine ⟨fun r hr _ h22 => h.other r ?_, h.sp, h.rd, h.wr, ?_⟩
  · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true, ne_eq, not_true_eq_false]
  · rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide) (by decide))

theorem InputArgs.keeps {s t : State} {offset : Nat} (h : VG.Proof.Argon2.AArch64.Initial.InputArgs s t offset) :
    VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  refine ⟨fun r hr h20 _ => h.other r ?_, h.sp, h.rd, h.wr, ?_⟩
  · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true, ne_eq, not_true_eq_false]
  · rw [h.mem]; exact Frame.refl _ _

theorem LengthArgs.prefix {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    bytesAt t.mem (s.gpr .x24 + 792) 4 = Spec.Argon2.le32 (VG.Proof.Argon2.AArch64.Initial.wordAt s offset).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl), h.mem,
    Mem.readW_writeW_self32]
  rfl

theorem LengthArgs.repr {s t : State} {offset : Nat} (h : LengthArgs s offset t)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .x24) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .x24) d := by
  rw [h.keeps.x24]
  apply Proof.Blake2.AArch64.Stream.repr_congr Proof.Blake2.AArch64.Stream.okB
    (mem := s.mem) (h := repr)
  intro i hi
  have f : Frame [⟨s.gpr .x24 + 792, 4⟩] s.mem t.mem := by
    rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply f.bytes (R := ⟨s.gpr .x24, 192⟩) _ (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem InputArgs.repr {s t : State} {offset : Nat} (h : VG.Proof.Argon2.AArch64.Initial.InputArgs s t offset)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .x24) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .x24) d := by
  rw [h.keeps.x24, h.mem]; exact repr

theorem addCount_ok (s : State) :
    WP isa (.block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) s fun t =>
      t.gpr .x20 = s.gpr .x20 + s.gpr .x22 ∧ t.mem = s.mem ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.add, Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, fun r hr h20 _ => ?_, rfl, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .x15 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_write, h20, hn, ite_false]

end VG.Proof.Argon2.AArch64.Initial
end

/-! # H₀: absorb a length-prefixed byte-string input -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

theorem slots_aligned (d : Nat) (hd : d ∈ VG.Proof.Argon2.AArch64.Initial.slots) : d % 8 = 0 := by
  have all : ∀ d ∈ VG.Proof.Argon2.AArch64.Initial.slots, d % 8 = 0 := by decide
  exact all d hd

structure InputReady (s : State) (po lo : Nat) : Prop where
  space : VG.Proof.Argon2.AArch64.Initial.Space s
  pointerSlot : po ∈ VG.Proof.Argon2.AArch64.Initial.slots
  lengthSlot : lo ∈ VG.Proof.Argon2.AArch64.Initial.slots
  pointerBound : po + 8 ≤ 272
  lengthBound : lo + 8 ≤ 272
  length : (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat < 2 ^ 32
  cover : Covers [VG.Proof.Argon2.AArch64.Initial.inputRegion s po lo] (s.rd ++ s.wr)
  work : (VG.Proof.Argon2.AArch64.Initial.inputRegion s po lo).Disjoint ⟨s.gpr .x24, 16384⟩
  stack : (VG.Proof.Argon2.AArch64.Initial.inputRegion s po lo).Disjoint (below (s.sp) 16)

theorem InputReady.keeps {s t : State} {po lo : Nat} (h : VG.Proof.Argon2.AArch64.Initial.InputReady s po lo)
    (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) : VG.Proof.Argon2.AArch64.Initial.InputReady t po lo := by
  have reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
  refine ⟨h.space.keeps k, h.pointerSlot, h.lengthSlot, h.pointerBound, h.lengthBound,
    ?_, ?_, ?_, ?_⟩
  · rw [h.space.word_keeps k lo h.lengthBound]; exact h.length
  · rw [reg, k.rd, k.wr]; exact h.cover
  · rw [reg, k.x24]; exact h.work
  · rw [reg, k.sp]; exact h.stack

def inputBytes (s : State) (po lo : Nat) : List Byte :=
  bytesAt s.mem (VG.Proof.Argon2.AArch64.Initial.wordAt s po) (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat

theorem inputBytes_length (s : State) (po lo : Nat) :
    (VG.Proof.Argon2.AArch64.Initial.inputBytes s po lo).length = (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat := by
  simp only [VG.Proof.Argon2.AArch64.Initial.inputBytes, bytesAt, List.length_map, List.length_range]

theorem InputReady.bytes_keeps {s t : State} {po lo : Nat} (h : VG.Proof.Argon2.AArch64.Initial.InputReady s po lo)
    (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) : VG.Proof.Argon2.AArch64.Initial.inputBytes t po lo = VG.Proof.Argon2.AArch64.Initial.inputBytes s po lo := by
  unfold VG.Proof.Argon2.AArch64.Initial.inputBytes
  rw [h.space.word_keeps k po h.pointerBound, h.space.word_keeps k lo h.lengthBound]
  exact k.bytes (VG.Proof.Argon2.AArch64.Initial.inputRegion s po lo) h.work h.stack (by
    change (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat ≤ 2 ^ 64
    exact Nat.le_of_lt (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).isLt)

theorem absorb_ok (v : HPrime.Backend) (s : State) (po lo : Nat)
    (h : VG.Proof.Argon2.AArch64.Initial.InputReady s po lo) (d : List Byte)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length)
    (bound : d.length + 4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat < 2 ^ 64) :
    WP isa (absorb v.hash po lo) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .x24)
        (appendInput d (VG.Proof.Argon2.AArch64.Initial.inputBytes s po lo)) ∧
      t.gpr .x20 = BitVec.ofNat 64 (appendInput d (VG.Proof.Argon2.AArch64.Initial.inputBytes s po lo)).length ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  unfold absorb
  refine WP.seq ((lengthArgs_ok s lo (VG.Proof.Argon2.AArch64.Initial.slots_aligned lo h.lengthSlot) (by have := h.lengthBound; omega) (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  have hA := h.keeps ka
  have lenA : (a.gpr .x3).toNat = 4 := by rw [ha.size]; rfl
  have dataA : Covers [⟨a.gpr .x2, (a.gpr .x3).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.x24.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .x24, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  have dsA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 192⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  have dwA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24 + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x2, (a.gpr .x3).toNat⟩ := by
    rw [ha.pointer, lenA, ka.x24.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega) hA.space.stackMinimum hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : VG.Proof.Argon2.AArch64.Initial.Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.update_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  have prefixA : bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat =
      Spec.Argon2.le32 (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  have r12U : u.gpr .x20 = s.gpr .x20 :=
    (regsU _ (by decide) (by decide)).trans (ha.other _ (by decide))
  have r14U : u.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo := (regsU _ (by decide) (by decide)).trans ha.length
  refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.inputArgs_ok u po (VG.Proof.Argon2.AArch64.Initial.slots_aligned po h.pointerSlot) (by have := h.pointerBound; omega) (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  have ksx := ksu.trans kux
  have hX := h.keeps ksx
  have srcX : x.gpr .x2 = VG.Proof.Argon2.AArch64.Initial.wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  have lenX : x.gpr .x3 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo := hx.length.trans r14U
  have r14X : x.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo :=
    (hx.other _ (by decide)).trans r14U
  have reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .x24)
      (d ++ Spec.Argon2.le32 (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.x24]
    simpa only [prefixA] using reprU
  have prefixLen : (d ++ Spec.Argon2.le32 (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  have countX : x.gpr .x1 = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  have coverX : Covers [⟨x.gpr .x2, (x.gpr .x3).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  have dsX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24, 192⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  have dwX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24 + 192, 576⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  have sdX : (below (x.sp) 16).Disjoint ⟨x.gpr .x2, (x.gpr .x3).toNat⟩ := by
    rw [srcX, lenX, ksx.sp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.stackMinimum hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, spY, frameY⟩
  have ky : VG.Proof.Argon2.AArch64.Initial.Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, spY, HPrime.update_frame _ _ frameY⟩
  have ksy := ksx.trans ky
  have r12Y : y.gpr .x20 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide) (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  have r14Y : y.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo := (regsY _ (by decide) (by decide)).trans r14X
  have bytesX : bytesAt x.mem (x.gpr .x2) (x.gpr .x3).toNat = VG.Proof.Argon2.AArch64.Initial.inputBytes s po lo := by
    rw [srcX, lenX]
    exact ksx.bytes (VG.Proof.Argon2.AArch64.Initial.inputRegion s po lo) h.work h.stack (Nat.le_of_lt (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).isLt)
  refine (VG.Proof.Argon2.AArch64.Initial.addCount_ok y).mono ?_
  rintro t ⟨ht12, hm, kt⟩
  refine ⟨?_, ?_, ksy.trans kt⟩
  · rw [kt.x24, hm, ky.x24]
    simpa only [appendInput, VG.Proof.Argon2.AArch64.Initial.inputBytes_length, bytesX] using reprY
  · have hw : BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Initial.wordAt s lo).toNat = VG.Proof.Argon2.AArch64.Initial.wordAt s lo := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ht12, r12Y, r14Y, ← hw, ← BitVec.ofNat_add,
      Proof.Argon2.appendInput_length, VG.Proof.Argon2.AArch64.Initial.inputBytes_length]

end VG.Proof.Argon2.AArch64.Initial

end

/-! # H₀: initialize BLAKE2b and absorb the public parameter header -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def headerBytes (s : State) : List Byte :=
  (List.range 6).flatMap fun j => Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s j)

theorem headerBytes_keeps {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) :
    VG.Proof.Argon2.AArch64.Initial.headerBytes t = VG.Proof.Argon2.AArch64.Initial.headerBytes s := by
  unfold VG.Proof.Argon2.AArch64.Initial.headerBytes
  simp only [List.flatMap]
  apply congrArg List.flatten
  exact List.map_congr_left fun j _ => congrArg Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue_keeps h k j)

theorem headerBytes_length (s : State) : (VG.Proof.Argon2.AArch64.Initial.headerBytes s).length = 24 := by
  unfold VG.Proof.Argon2.AArch64.Initial.headerBytes
  change (Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s 0) ++ Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s 1) ++
    Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s 2) ++ Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s 3) ++
    Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s 4) ++ Spec.Blake2.wordBytes (VG.Proof.Argon2.AArch64.Initial.headerValue s 5)).length = 24
  simp only [Spec.Blake2.wordBytes, List.length_append, List.length_map, List.length_range]

theorem digestLength_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten) s fun t =>
      t.gpr .x1 = 64 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  refine (SegmentSetup.register_ok s .x1 64 (by decide)).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r hr h30 => keeps.regs r ?_, keeps.rd, keeps.wr, keeps.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem initialCount_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten) s fun t =>
      t.gpr .x20 = 24 ∧ t.mem = s.mem ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  refine (SegmentSetup.register_ok s .x20 24 (by decide)).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r _ h20 _ => keeps.regs r ?_, keeps.sp, keeps.rd, keeps.wr, ?_⟩
  · simpa only [List.mem_singleton] using h20
  · rw [keeps.mem]; exact Frame.refl _ _

theorem start_ok (v : HPrime.Backend) (s : State) (h : VG.Proof.Argon2.AArch64.Initial.Space s) :
    WP isa (start v.hash) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .x24) (VG.Proof.Argon2.AArch64.Initial.headerBytes s) ∧
      t.gpr .x20 = 24 ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  unfold start headerCode
  refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.digestLength_ok s).mono ?_)
  rintro a ⟨lenA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : VG.Proof.Argon2.AArch64.Initial.Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .x24) [] := by
    rw [kw.x24]
    apply Proof.Blake2.AArch64.Stream.repr_congr Proof.Blake2.AArch64.Stream.okB
      (mem := u.mem) (h := by simpa only [lenA, ku.x24, show (64 : BitVec 64).toNat = 64 from rfl] using reprU)
    intro i hi
    rw [memW]
    apply (VG.Proof.Argon2.AArch64.Initial.headerMem_frame u 6 (by decide)).bytes (R := ⟨u.gpr .x24, 192⟩) _
      (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint _ (by decide) (by decide)
  have headW : bytesAt w.mem (w.gpr .x24 + 768) 24 = VG.Proof.Argon2.AArch64.Initial.headerBytes s := by
    rw [kw.x24, memW, VG.Proof.Argon2.AArch64.Initial.headerMem_bytes]
    exact VG.Proof.Argon2.AArch64.Initial.headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) hW.stackMinimum (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  have kx := Keeps.of_hash kx'
  have ksx := ksw.trans kx
  refine (VG.Proof.Argon2.AArch64.Initial.initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.x24, memT, kx.x24]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.AArch64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Initial`. -/
section

/-! Merged from `Proof.Argon2.AArch64.InitialFinish`. -/
section
/-! # H₀: finalize BLAKE2b and copy the digest into the derivation frame -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

structure Finished (s t : State) : Prop where
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x20 → r ≠ .x22 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x24, 832⟩, below (s.sp) 16, ⟨s.gpr .x19, 64⟩] s.mem t.mem

theorem finishCount_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten) s fun t =>
      t.gpr .x1 = s.gpr .x20 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  refine (Instructions.mov_ok s .x1 .x20).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r hr _ => keeps.regs r ?_, keeps.rd, keeps.wr, keeps.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem finishOutput_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.mov .x22 .x19,
      Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten) s fun t =>
      t.gpr .x22 = s.gpr .x19 ∧ t.gpr .x8 = 64 ∧ t.mem = s.mem ∧ VG.Proof.Argon2.AArch64.Initial.Keeps s t := by
  rw [List.flatten_cons, List.flatten_cons, List.flatten_nil,
    List.append_nil, WP.block_append_iff]
  refine (Instructions.mov_ok s .x22 .x19).mono ?_
  rintro a ⟨value, ka⟩
  have im := SegmentSetup.register_ok a .x8 64 (by decide)
  change WP isa (.block (Impl.Argon2.AArch64.Instructions.imm .x8 64)) a _ at im
  refine im.mono ?_
  rintro t ⟨count, kt⟩
  refine ⟨(kt.regs .x22 (by decide)).trans value, count, kt.mem.trans ka.mem,
    fun r hr _ h22 => ?_, kt.sp.trans ka.sp, kt.rd.trans ka.rd, kt.wr.trans ka.wr, ?_⟩
  · have h8 : r ≠ .x8 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (kt.regs r (by simpa only [List.mem_singleton] using h8)).trans
      (ka.regs r (by simpa only [List.mem_singleton] using h22))
  · rw [kt.mem, ka.mem]; exact Frame.refl _ _

theorem finish_ok (v : HPrime.Backend) (s : State) (h : VG.Proof.Argon2.AArch64.Initial.Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (VG.Impl.Argon2.AArch64.Initial.finish v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      VG.Proof.Argon2.AArch64.Initial.Finished s t := by
  unfold VG.Impl.Argon2.AArch64.Initial.finish
  refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .x24) d := by
    rw [memA, ka.x24]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.stackMinimum hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, spU, frameU⟩
  have ku : VG.Proof.Argon2.AArch64.Initial.Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.finalize_frame _ _ frameU⟩
  have ksu := ka.trans ku
  refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have outW : ∀ i < 64, InRegions w.wr (w.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.x19]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]; exact hi)⟩
  have sepW : (⟨w.gpr .x24 + 768, 64⟩ : Region).Disjoint ⟨w.gpr .x22, 64⟩ := by
    rw [dstW, ← kw.x19]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  have sourceLength : (bytesAt w.mem (w.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.sp.trans ksw.sp, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .x22 = s.gpr .x19 := dstW.trans ksu.x19
    rw [ht.mem]
    conv_lhs => arg 2; rw [← dst]
    have copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .x22)
      (bytesAt w.mem (w.gpr .x24 + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.x24, ku.x24]
    exact digestU
  · have hrax : r ≠ .x8 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .x3 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .x2 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r hrax hrcx hrdx h14).trans (ksw.regs r hr h12 h14)
  · apply Frame.trans (ksw.frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))))
    apply ht.frame.mono
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [dstW, ksu.x19]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end VG.Proof.Argon2.AArch64.Initial
end

/-! # Correctness of H₀ for every verified BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

abbrev inputs : List (Nat × Nat) :=
  [(passwordOffset, passwordLenOffset), (saltOffset, saltLenOffset),
   (secretOffset, secretLenOffset), (adOffset, adLenOffset)]

def message (s : State) (ps : List (Nat × Nat)) (d : List Byte) : List Byte :=
  ps.foldl (fun m p => appendInput m (VG.Proof.Argon2.AArch64.Initial.inputBytes s p.1 p.2)) d

def inputSize (s : State) (ps : List (Nat × Nat)) : Nat :=
  (ps.map fun p => 4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s p.2).toNat).sum

def remaining (h : VG.Impl.Argon2.AArch64.HPrime.Hash) : List (Nat × Nat) → Prog isa
  | [] => VG.Impl.Argon2.AArch64.Initial.finish h
  | p :: ps => .seq (absorb h p.1 p.2) (VG.Proof.Argon2.AArch64.Initial.remaining h ps)

theorem message_keeps {s t : State} (ps : List (Nat × Nat)) (d : List Byte)
    (ready : ∀ p ∈ ps, VG.Proof.Argon2.AArch64.Initial.InputReady s p.1 p.2) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) :
    VG.Proof.Argon2.AArch64.Initial.message t ps d = VG.Proof.Argon2.AArch64.Initial.message s ps d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    simp only [VG.Proof.Argon2.AArch64.Initial.message, List.foldl_cons]
    rw [(ready p (by simp only [List.mem_cons, true_or])).bytes_keeps k]
    exact ih _ (fun q hq => ready q (List.mem_cons_of_mem p hq))

theorem inputSize_keeps {s t : State} (ps : List (Nat × Nat))
    (ready : ∀ p ∈ ps, VG.Proof.Argon2.AArch64.Initial.InputReady s p.1 p.2) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) :
    VG.Proof.Argon2.AArch64.Initial.inputSize t ps = VG.Proof.Argon2.AArch64.Initial.inputSize s ps := by
  unfold VG.Proof.Argon2.AArch64.Initial.inputSize
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [(ready p hp).space.word_keeps k p.2 (ready p hp).lengthBound]

theorem Finished.before {s u t : State} (k : VG.Proof.Argon2.AArch64.Initial.Keeps s u) (f : VG.Proof.Argon2.AArch64.Initial.Finished u t) : VG.Proof.Argon2.AArch64.Initial.Finished s t := by
  refine ⟨fun r hr h12 h14 => (f.regs r hr h12 h14).trans (k.regs r hr h12 h14),
    f.sp.trans k.sp, f.rd.trans k.rd, f.wr.trans k.wr, ?_⟩
  apply (k.frame.mono ?_).trans
  · simpa only [k.x24, k.sp, k.x19] using f.frame
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem remaining_ok (v : HPrime.Backend) (ps : List (Nat × Nat))
    (s : State) (space : VG.Proof.Argon2.AArch64.Initial.Space s) (ready : ∀ p ∈ ps, VG.Proof.Argon2.AArch64.Initial.InputReady s p.1 p.2)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length)
    (bound : d.length + VG.Proof.Argon2.AArch64.Initial.inputSize s ps < 2 ^ 64) :
    WP isa (VG.Proof.Argon2.AArch64.Initial.remaining v.hash ps) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 =
        Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) (VG.Proof.Argon2.AArch64.Initial.message s ps d) ∧ VG.Proof.Argon2.AArch64.Initial.Finished s t := by
  induction ps generalizing s d with
  | nil =>
    exact VG.Proof.Argon2.AArch64.Initial.finish_ok v s space d repr count (by simpa only [VG.Proof.Argon2.AArch64.Initial.inputSize, List.map_nil,
                                      List.sum_nil, Nat.add_zero] using bound)
  | cons p ps ih =>
    have hp := ready p (by simp only [List.mem_cons, true_or])
    have tailReady : ∀ q ∈ ps, VG.Proof.Argon2.AArch64.Initial.InputReady s q.1 q.2 := fun q hq =>
      ready q (List.mem_cons_of_mem p hq)
    have size : VG.Proof.Argon2.AArch64.Initial.inputSize s (p :: ps) = 4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s p.2).toNat + VG.Proof.Argon2.AArch64.Initial.inputSize s ps := rfl
    refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.absorb_ok v s p.1 p.2 hp d repr count (by rw [size] at bound; omega)).mono ?_)
    rintro u ⟨reprU, countU, ku⟩
    refine (ih u (space.keeps ku) (fun q hq => (tailReady q hq).keeps ku)
      _ reprU countU ?_).mono ?_
    · rw [VG.Proof.Argon2.AArch64.Initial.inputSize_keeps ps tailReady ku, Proof.Argon2.appendInput_length, VG.Proof.Argon2.AArch64.Initial.inputBytes_length]
      rw [size] at bound; omega
    · rintro t ⟨digestT, ft⟩
      refine ⟨?_, ft.before ku⟩
      rw [ku.x19] at digestT
      rw [VG.Proof.Argon2.AArch64.Initial.message_keeps ps _ tailReady ku] at digestT
      exact digestT

theorem code_ok (v : HPrime.Backend) (s : State) (space : VG.Proof.Argon2.AArch64.Initial.Space s)
    (ready : ∀ p ∈ VG.Proof.Argon2.AArch64.Initial.inputs, VG.Proof.Argon2.AArch64.Initial.InputReady s p.1 p.2) :
    WP isa (VG.Impl.Argon2.AArch64.Initial.code v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 =
        Spec.Argon2.H 64 (VG.Proof.Argon2.AArch64.Initial.message s VG.Proof.Argon2.AArch64.Initial.inputs (VG.Proof.Argon2.AArch64.Initial.headerBytes s)) ∧ VG.Proof.Argon2.AArch64.Initial.Finished s t := by
  change WP isa (.seq (start v.hash) (VG.Proof.Argon2.AArch64.Initial.remaining v.hash VG.Proof.Argon2.AArch64.Initial.inputs)) s _
  refine WP.seq ((VG.Proof.Argon2.AArch64.Initial.start_ok v s space).mono ?_)
  rintro u ⟨reprU, countU, ku⟩
  have count : u.gpr .x20 = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Initial.headerBytes s).length := by
    rw [VG.Proof.Argon2.AArch64.Initial.headerBytes_length]; exact countU
  have bound : (VG.Proof.Argon2.AArch64.Initial.headerBytes s).length + VG.Proof.Argon2.AArch64.Initial.inputSize s VG.Proof.Argon2.AArch64.Initial.inputs < 2 ^ 64 := by
    have hp := (ready (passwordOffset, passwordLenOffset) (by decide)).length
    have hs := (ready (saltOffset, saltLenOffset) (by decide)).length
    have hk := (ready (secretOffset, secretLenOffset) (by decide)).length
    have ha := (ready (adOffset, adLenOffset) (by decide)).length
    simp only at hp hs hk ha
    rw [VG.Proof.Argon2.AArch64.Initial.headerBytes_length]
    change 24 + (4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s passwordLenOffset).toNat +
      (4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s saltLenOffset).toNat + (4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s secretLenOffset).toNat +
      (4 + (VG.Proof.Argon2.AArch64.Initial.wordAt s adLenOffset).toNat + 0)))) < 2 ^ 64
    omega
  refine (VG.Proof.Argon2.AArch64.Initial.remaining_ok v VG.Proof.Argon2.AArch64.Initial.inputs u (space.keeps ku) (fun p hp => (ready p hp).keeps ku)
    _ reprU count (by rw [VG.Proof.Argon2.AArch64.Initial.inputSize_keeps VG.Proof.Argon2.AArch64.Initial.inputs ready ku]; exact bound)).mono ?_
  rintro t ⟨digestT, ft⟩
  refine ⟨?_, ft.before ku⟩
  rw [ku.x19, VG.Proof.Argon2.AArch64.Initial.message_keeps VG.Proof.Argon2.AArch64.Initial.inputs _ ready ku] at digestT
  rw [Proof.Argon2.H_stream, ← digestT]
  exact (List.take_of_length_le (by simp only [bytesAt, List.length_map, List.length_range,
    Nat.le_refl])).symm

/-- The public header is supplied by the enclosing argument-validation proof.
The byte-string contents remain unrestricted. -/
theorem initialHash_ok (v : HPrime.Backend) (s : State) (space : VG.Proof.Argon2.AArch64.Initial.Space s)
    (ready : ∀ p ∈ VG.Proof.Argon2.AArch64.Initial.inputs, VG.Proof.Argon2.AArch64.Initial.InputReady s p.1 p.2) (p : Spec.Argon2.Params)
    (header : VG.Proof.Argon2.AArch64.Initial.headerBytes s = Proof.Argon2.initialHeader p) :
    WP isa (VG.Impl.Argon2.AArch64.Initial.code v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 = Spec.Argon2.initialHash p
        (VG.Proof.Argon2.AArch64.Initial.inputBytes s passwordOffset passwordLenOffset) (VG.Proof.Argon2.AArch64.Initial.inputBytes s saltOffset saltLenOffset)
        (VG.Proof.Argon2.AArch64.Initial.inputBytes s secretOffset secretLenOffset) (VG.Proof.Argon2.AArch64.Initial.inputBytes s adOffset adLenOffset) ∧
      VG.Proof.Argon2.AArch64.Initial.Finished s t := by
  refine (VG.Proof.Argon2.AArch64.Initial.code_ok v s space ready).mono ?_
  rintro t ⟨digest, frame⟩
  refine ⟨?_, frame⟩
  rw [header] at digest
  exact digest

end VG.Proof.Argon2.AArch64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialBody`. -/
section

/-! Merged from `Proof.Argon2.AArch64.InitialMetadata`. -/
section
/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

theorem Finished.x19 {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Finished s t) : t.gpr .x19 = s.gpr .x19 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.x24 {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Finished s t) : t.gpr .x24 = s.gpr .x24 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Finished s t) (space : VG.Proof.Argon2.AArch64.Initial.Space s)
    (d : Nat) (bound : d + 8 ≤ 272) (afterDigest : 64 ≤ d) : VG.Proof.Argon2.AArch64.Initial.wordAt t d = VG.Proof.Argon2.AArch64.Initial.wordAt s d := by
  unfold VG.Proof.Argon2.AArch64.Initial.wordAt
  rw [h.x19]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact space.frameWork.sub_left (Offset.sub_base _ bound) |>.sub_right
      (Region.sub_prefix (by decide))
  · exact space.frameStack.sub_left (Offset.sub_base _ bound)
  · simpa only [BitVec.add_zero] using
      Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 64)
        (Or.inr afterDigest) (by omega) (by decide)

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialBodyReady`. -/
section
/-! H₀ retains the allocation and parameter environment of complete derivation. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2

theorem hashed_environment {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word space 248 (by decide) (by decide)
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.x19 done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.x19]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.x19, work]; exact e.addressLayout.frameWork
    · rw [done.x19, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.x19]; exact e.reads
  · rw [done.wr, done.x19]; exact e.counterWrite
  · rw [done.wr, done.x19]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word space 240 (by decide) (by decide)).trans e.blocksWord
  · exact (done.frame_word space 72 (by decide) (by decide)).trans e.passesWord
  · exact (done.frame_word space 112 (by decide) (by decide)).trans e.variantWord
  · exact (done.frame_word space 184 (by decide) (by decide)).trans e.lanesWord

theorem hashed_output {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word space 232 (by decide) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word space 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨(by rw [done.sp]; exact h.output.stackMinimum), h.output.positive, h.output.bound, ?_,
    (done.frame_word space 264 (by decide) (by decide)).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.x19]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem hashed_ready {s t : State} {p : Params} (h : InitFill.Ready p s)
    (space : Initial.Space s) (done : Initial.Finished s t) : InitFill.Ready p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨?_, VG.Proof.Argon2.AArch64.InitialBody.hashed_environment h space done, VG.Proof.Argon2.AArch64.InitialBody.hashed_output h space done, h.positive, ?_⟩
  · constructor
    · rw [base]
      exact h.initializing.space.same done.wr done.x19 done.x24 done.sp
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.memoryRead
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.lanesRead
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.blocksRead
    · exact (done.frame_word space 232 (by decide) (by decide)).trans h.initializing.memoryWord |>.trans base.symm
    · exact (done.frame_word space 184 (by decide) (by decide)).trans h.initializing.lanesWord
    · exact (done.frame_word space 240 (by decide) (by decide)).trans h.initializing.blocksWord
    · exact (done.regs .x21 (by decide) (by decide) (by decide)).trans h.initializing.laneLength
  · rw [done.x24, work]; exact h.scratch

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! H₀, initialization, every filling pass, and finalization agree with derive. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  hashSpace : Initial.Space s
  inputs : ∀ input ∈ Initial.inputs, Initial.InputReady s input.1 input.2
  header : Initial.headerBytes s = Proof.Argon2.initialHeader p
  filling : InitFill.Ready p s

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = derive p
    (Initial.inputBytes s passwordOffset passwordLenOffset)
    (Initial.inputBytes s saltOffset saltLenOffset)
    (Initial.inputBytes s secretOffset secretLenOffset)
    (Initial.inputBytes s adOffset adLenOffset)
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (InitFill.writes s p) s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem hash_frame {s t : State} {p : Params} (h : InitFill.Ready p s) (done : Initial.Finished s t) :
    Frame (InitFill.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [InitFill.writes], by
      rw [h.scratch]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.sp) 16, by simp [InitFill.writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .x19, 72⟩, by simp [InitFill.writes], Region.sub_prefix (by decide)⟩

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params) (h : VG.Proof.Argon2.AArch64.InitialBody.Ready p s) :
    WP isa (Impl.Argon2.AArch64.InitialBody.code name v.hash) s (VG.Proof.Argon2.AArch64.InitialBody.Done s · p) := by
  unfold Impl.Argon2.AArch64.InitialBody.code
  refine WP.seq ((Initial.initialHash_ok v s h.hashSpace h.inputs p h.header).mono ?_)
  rintro a ⟨digest, hashed⟩
  refine (InitFill.code_ok v name a p (VG.Proof.Argon2.AArch64.InitialBody.hashed_ready h.filling h.hashSpace hashed)).mono ?_
  intro t filled
  have base : FillKernel.matrix a = FillKernel.matrix s := hashed.frame_word h.hashSpace 232 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := hashed.frame_word h.hashSpace 248 (by decide) (by decide)
  have output : FinalOutput.output a = FinalOutput.output s := hashed.frame_word h.hashSpace 256 (by decide) (by decide)
  refine ⟨?_, filled.bp.trans hashed.x19, filled.sp.trans hashed.sp,
    filled.rd.trans hashed.rd, filled.wr.trans hashed.wr, ?_, ?_⟩
  · have result := filled.digest
    rw [output, hashed.x19, digest, InitFill.result_derive] at result
    exact result
  · have frame := filled.frame
    rw [InitFill.writes_eq s a p hashed.x19 hashed.sp base work output] at frame
    exact (VG.Proof.Argon2.AArch64.InitialBody.hash_frame h.filling hashed).trans frame
  · intro r hr
    have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
        r ∈ FillCompress.loopRegs ∧ r ≠ .x20 ∧ r ≠ .x22 := by decide
    obtain ⟨member, h20, h22⟩ := facts r hr
    exact (filled.unused r hr).trans (hashed.regs r member h20 h22)

end VG.Proof.Argon2.AArch64.InitialBody

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialBodyState`. -/
section

/-! The complete body depends on the frame, allocation, and computed lane length. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2

structure SameFrame (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  bx : t.gpr .x24 = s.gpr .x24
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem SameFrame.word {s t : State} (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t) (d : Nat) :
    Initial.wordAt t d = Initial.wordAt s d := by
  unfold Initial.wordAt; rw [k.mem, k.bp]

theorem SameFrame.inputBytes {s t : State} (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t) (po lo : Nat) :
    Initial.inputBytes t po lo = Initial.inputBytes s po lo := by
  unfold Initial.inputBytes; rw [k.word po, k.word lo, k.mem]

theorem SameFrame.hashSpace {s t : State} (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t)
    (h : Initial.Space s) : Initial.Space t := by
  constructor
  · rw [k.sp]; exact h.stackMinimum
  · rw [k.bx, k.wr]; exact h.work
  · rw [k.sp, k.bx]; exact h.stackWork
  · rw [k.bp, k.bx]; exact h.frameWork
  · rw [k.bp, k.sp]; exact h.frameStack
  · rw [k.rd, k.wr, k.bp]; exact h.readable
  · rw [k.wr, k.bp]; exact h.output

theorem SameFrame.input {s t : State} (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t) {po lo : Nat}
    (h : Initial.InputReady s po lo) : Initial.InputReady t po lo := by
  have word : ∀ d, Initial.wordAt t d = Initial.wordAt s d := by
    intro d; unfold Initial.wordAt; rw [k.mem, k.bp]
  have region : Initial.inputRegion t po lo = Initial.inputRegion s po lo := by
    unfold Initial.inputRegion; rw [word po, word lo]
  refine ⟨k.hashSpace h.space, h.pointerSlot, h.lengthSlot, h.pointerBound,
    h.lengthBound, ?_, ?_, ?_, ?_⟩
  · rw [word lo]; exact h.length
  · rw [region, k.rd, k.wr]; exact h.cover
  · rw [region, k.bx]; exact h.work
  · rw [region, k.sp]; exact h.stack

theorem SameFrame.output {s t : State} (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t) {p : Params}
    (h : FinalOutput.Ready p s) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := by
    unfold ReductionState.matrix; rw [k.mem, k.bp]
  have work : FinalOutput.work t = FinalOutput.work s := by
    unfold FinalOutput.work; rw [k.mem, k.bp]
  have output : FinalOutput.output t = FinalOutput.output s := by
    unfold FinalOutput.output; rw [k.mem, k.bp]
  refine ⟨by rw [k.sp]; exact h.stackMinimum, h.positive, h.bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.rd, k.wr, k.bp]; exact h.reads
  · rw [k.mem, k.bp]; exact h.tagWord
  · rw [base, k.rd, k.wr]; exact h.input
  · rw [output, k.wr]; exact h.outputWrite
  · rw [work, k.wr]; exact h.workWrite
  · rw [base, work]; exact h.inputWork
  · rw [output, work]; exact h.outputWork
  · rw [k.sp, base]; exact h.stackInput
  · rw [k.sp, output]; exact h.stackOutput
  · rw [k.sp, work]; exact h.stackWork

theorem SameFrame.filling {s t : State} (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t) {p : Params}
    (h : InitFill.Ready p s) (laneLength : t.gpr .x21 = BitVec.ofNat 64 p.laneLen) :
    InitFill.Ready p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.bp]
  have work : FinalOutput.work t = FinalOutput.work s := by
    unfold FinalOutput.work; rw [k.mem, k.bp]
  refine ⟨?_, h.environment.of_state k.bp k.sp k.mem k.rd k.wr,
    k.output h.output, h.positive, ?_⟩
  · constructor
    · rw [base]; exact h.initializing.space.same k.wr k.bp k.bx k.sp
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.memoryRead
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.lanesRead
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.blocksRead
    · unfold Initial.wordAt; rw [k.mem, k.bp, base]; exact h.initializing.memoryWord
    · unfold Initial.wordAt; rw [k.mem, k.bp]; exact h.initializing.lanesWord
    · unfold Initial.wordAt; rw [k.mem, k.bp]; exact h.initializing.blocksWord
    · exact laneLength
  · rw [k.bx, work]; exact h.scratch

theorem Ready.of_state {s t : State} {p : Params} (h : VG.Proof.Argon2.AArch64.InitialBody.Ready p s)
    (k : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s t) (laneLength : t.gpr .x21 = BitVec.ofNat 64 p.laneLen) : VG.Proof.Argon2.AArch64.InitialBody.Ready p t := by
  refine ⟨k.hashSpace h.hashSpace, fun input hi => k.input (h.inputs input hi), ?_,
    k.filling h.filling laneLength⟩
  have header : Initial.headerBytes t = Initial.headerBytes s := by
    unfold Initial.headerBytes
    simp only [Initial.headerValue, Initial.wordAt, k.mem, k.bp]
  exact header.trans h.header

end VG.Proof.Argon2.AArch64.InitialBody

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.InitialBodyReviewedState`. -/
section

/-! Merged from `Proof.Argon2.AArch64.InitialCTState`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialBlocksCT`. -/
section
/-! # Constant time of H₀ header and input argument preparation

Only frame and scratch addresses affect these blocks' execution traces.
The relational proof of the complete derivation additionally tracks public
lengths and pointers across its BLAKE2b calls.
-/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

def AgreeBases (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19 ∧ s.gpr .x24 = t.gpr .x24

theorem agreeBases_taint {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.AgreeBases s t) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x24]) s t := by
  refine ⟨h.1, ?_⟩
  intro r hr
  simp only [Taint.ofRegs, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.1
  · exact h.2.2

theorem header_rel : RelCT isa VG.Proof.Argon2.AArch64.Initial.AgreeBases headerCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x19, .x24])
    (fun _ _ h => VG.Proof.Argon2.AArch64.Initial.agreeBases_taint h) (by taint_decide)

theorem lengthArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24])
      (.block (lengthArgs offset)) hint).isSome = true) :
    RelCT isa VG.Proof.Argon2.AArch64.Initial.AgreeBases (.block (lengthArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.x19, .x24])
    (fun _ _ h => VG.Proof.Argon2.AArch64.Initial.agreeBases_taint h) check

theorem inputArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.x19])
      (.block (inputArgs offset)) hint).isSome = true) :
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.1, by
      intro r hr; simp only [Taint.ofRegs, RegSet.mem_ofList, List.mem_singleton] at hr; subst r; exact h.2⟩) check

/-- All four concrete input blocks use their checked public base address. -/
theorem inputs_rel :
    RelCT isa VG.Proof.Argon2.AArch64.Initial.AgreeBases (.block (lengthArgs passwordLenOffset)) (fun _ _ => True) ∧
    RelCT isa VG.Proof.Argon2.AArch64.Initial.AgreeBases (.block (lengthArgs saltLenOffset)) (fun _ _ => True) ∧
    RelCT isa VG.Proof.Argon2.AArch64.Initial.AgreeBases (.block (lengthArgs secretLenOffset)) (fun _ _ => True) ∧
    RelCT isa VG.Proof.Argon2.AArch64.Initial.AgreeBases (.block (lengthArgs adLenOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs passwordOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs saltOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs secretOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs adOffset)) (fun _ _ => True) :=
  ⟨VG.Proof.Argon2.AArch64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.AArch64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.AArch64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.AArch64.Initial.lengthArgs_rel _ ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.AArch64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.AArch64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩,
    VG.Proof.Argon2.AArch64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩, VG.Proof.Argon2.AArch64.Initial.inputArgs_rel _ ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.AArch64.Initial
end

/-! Public input metadata survives every hash call without relating input bytes. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

structure Ready (s : State) : Prop where
  space : VG.Proof.Argon2.AArch64.Initial.Space s
  inputs : ∀ input ∈ VG.Proof.Argon2.AArch64.Initial.inputs, VG.Proof.Argon2.AArch64.Initial.InputReady s input.1 input.2

theorem Ready.keeps {s t : State} (h : VG.Proof.Argon2.AArch64.Initial.Ready s) (k : VG.Proof.Argon2.AArch64.Initial.Keeps s t) : VG.Proof.Argon2.AArch64.Initial.Ready t :=
  ⟨h.space.keeps k, fun p hp => (h.inputs p hp).keeps k⟩

structure Related (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.Initial.Ready s
  right : VG.Proof.Argon2.AArch64.Initial.Ready t
  bp : s.gpr .x19 = t.gpr .x19
  bx : s.gpr .x24 = t.gpr .x24
  sp : s.sp = t.sp
  words : ∀ d ∈ VG.Proof.Argon2.AArch64.Initial.slots, VG.Proof.Argon2.AArch64.Initial.wordAt s d = VG.Proof.Argon2.AArch64.Initial.wordAt t d

theorem Related.keeps {s₁ s₂ t₁ t₂ : State} (h : VG.Proof.Argon2.AArch64.Initial.Related s₁ s₂)
    (k₁ : VG.Proof.Argon2.AArch64.Initial.Keeps s₁ t₁) (k₂ : VG.Proof.Argon2.AArch64.Initial.Keeps s₂ t₂) : VG.Proof.Argon2.AArch64.Initial.Related t₁ t₂ := by
  refine ⟨h.left.keeps k₁, h.right.keeps k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.x19, k₂.x19, h.bp]
  · rw [k₁.x24, k₂.x24, h.bx]
  · rw [k₁.sp, k₂.sp, h.sp]
  · intro d hd
    have bound : ∀ d ∈ VG.Proof.Argon2.AArch64.Initial.slots, d + 8 ≤ 272 := by decide
    rw [h.left.space.word_keeps k₁ d (bound d hd), h.right.space.word_keeps k₂ d (bound d hd)]
    exact h.words d hd

def RelatedRegs (rs : List Reg) (s t : State) : Prop :=
  VG.Proof.Argon2.AArch64.Initial.Related s t ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem hash_keeps_rel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (saved : ∀ r ∈ rs, r ∈ preserved ∧ r ≠ .x30)
    (ct : RelCT isa P c (fun _ _ => True))
    (pre : ∀ s t, P s t → VG.Proof.Argon2.AArch64.Initial.RelatedRegs rs s t)
    (wp : ∀ s t, P s t → WP isa c s (HPrime.Keeps s) ∧ WP isa c t (HPrime.Keeps t)) :
    RelCT isa P c (VG.Proof.Argon2.AArch64.Initial.RelatedRegs rs) := by
  apply (ct.wpDep wp).mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ha, hb⟩
  have h := pre s t hp
  refine ⟨h.1.keeps (Keeps.of_hash ha) (Keeps.of_hash hb), ?_⟩
  intro r hr
  rw [ha.regs r (saved r hr).1 (saved r hr).2, hb.regs r (saved r hr).1 (saved r hr).2]
  exact h.2 r hr

theorem finalize_ready {s : State} (h : VG.Proof.Argon2.AArch64.Initial.Ready s) : HPrime.FinalizeReady s :=
  ⟨h.space.stackMinimum, h.space.work, h.space.stackWork⟩

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialUpdateReady`. -/
section
/-! Permissions for the two updates of each length-prefixed H₀ input. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

theorem prefix_update_ready {s t : State} {lo : Nat} (h : VG.Proof.Argon2.AArch64.Initial.Space s) (args : LengthArgs s lo t) :
    HPrime.UpdateReady t := by
  have k := args.keeps
  have ht := h.keeps k
  have len : (t.gpr .x3).toNat = 4 := by rw [args.size]; rfl
  refine ⟨ht.stackMinimum, ht.work, ?_, ?_, ?_, ht.stackWork, ?_⟩
  · rw [args.pointer, len, ← k.x24]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨t.gpr .x24, 16384⟩, List.mem_append_right _ ht.work, 792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  · rw [args.pointer, len, k.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  · rw [args.pointer, len, k.x24]
    exact Offset.disjoint _ (d := 792) (n := 4) (e := 192) (k := 576) (by decide) (by decide) (by decide)
  · rw [args.pointer, len, ← k.x24]
    exact ht.stackWork.sub_right (Offset.sub_base _ (by decide))

theorem input_update_ready {s t : State} {po lo : Nat} (h : VG.Proof.Argon2.AArch64.Initial.InputReady s po lo)
    (length : s.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo) (args : InputArgs s t po) : HPrime.UpdateReady t := by
  have k := args.keeps
  have ptr : t.gpr .x2 = VG.Proof.Argon2.AArch64.Initial.wordAt s po := args.pointer
  have len : t.gpr .x3 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo := args.length.trans length
  refine ⟨(h.space.keeps k).stackMinimum, (h.space.keeps k).work, ?_, ?_, ?_, (h.space.keeps k).stackWork, ?_⟩
  · rw [ptr, len, k.rd, k.wr]; exact h.cover
  · rw [ptr, len, k.x24]; exact h.work.sub_right (Region.sub_prefix (by decide))
  · rw [ptr, len, k.x24]; exact h.work.sub_right (Offset.sub_base _ (by decide))
  · rw [ptr, len, k.sp]; exact h.stack.symm

structure LengthRelated (lo : Nat) (s t : State) : Prop where
  related : VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20, .x22] s t
  leftLength : s.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt s lo
  rightLength : t.gpr .x22 = VG.Proof.Argon2.AArch64.Initial.wordAt t lo

theorem LengthRelated.hash_keeps {lo : Nat} {s t a b : State} (h : VG.Proof.Argon2.AArch64.Initial.LengthRelated lo s t)
    (bound : lo + 8 ≤ 272) (ka : HPrime.Keeps s a) (kb : HPrime.Keeps t b) : VG.Proof.Argon2.AArch64.Initial.LengthRelated lo a b := by
  refine ⟨⟨h.related.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_, ?_⟩
  · intro r hr
    have saved : ∀ r ∈ ([.x20, .x22] : List Reg), r ∈ preserved ∧ r ≠ .x30 := by decide
    rw [ka.regs r ((saved r hr).1) ((saved r hr).2), kb.regs r ((saved r hr).1) ((saved r hr).2)]
    exact h.related.2 r hr
  · rw [ka.regs .x22 (by decide) (by decide), h.related.1.left.space.word_keeps (Keeps.of_hash ka) lo bound]
    exact h.leftLength
  · rw [kb.regs .x22 (by decide) (by decide), h.related.1.right.space.word_keeps (Keeps.of_hash kb) lo bound]
    exact h.rightLength

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialStartCT`. -/
section
/-! H₀ initialization and its fixed parameter header have input-independent traces. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem digestLength_rel : RelCT isa VG.Proof.Argon2.AArch64.Initial.Related (.block ([Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten))
    (fun s t => VG.Proof.Argon2.AArch64.Initial.Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.AArch64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.AArch64.Initial.digestLength_ok s, VG.Proof.Argon2.AArch64.Initial.digestLength_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  exact ⟨hp.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), la, lb⟩

theorem init_hash_rel (v : HPrime.Backend) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.Initial.Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64)
      (Impl.Argon2.AArch64.HPrime.init v.hash) VG.Proof.Argon2.AArch64.Initial.Related := by
  have ready (s : State) (h : VG.Proof.Argon2.AArch64.Initial.Ready s) (len : s.gpr .x1 = 64) : HPrime.InitReady s :=
    ⟨by rw [len]; decide, h.space.work,
      (h.space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))⟩
  have ct := HPrime.init_rel v (P := fun s t => VG.Proof.Argon2.AArch64.Initial.Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64)
    (fun s t ⟨h, ls, lt⟩ => ⟨ready s h.left ls, ready t h.right lt,
      h.bx, ls.trans lt.symm, h.sp⟩)
  have result := VG.Proof.Argon2.AArch64.Initial.hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1, by simp⟩)
    (fun s t ⟨h, ls, lt⟩ => ⟨HPrime.init_keeps v s (ready s h.left ls), HPrime.init_keeps v t (ready t h.right lt)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem header_state_rel : RelCT isa VG.Proof.Argon2.AArch64.Initial.Related headerCode VG.Proof.Argon2.AArch64.Initial.Related := by
  have ct := (header_rel.mono (P' := VG.Proof.Argon2.AArch64.Initial.Related) (fun _ _ h => ⟨h.sp, h.bp, h.bx⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨VG.Proof.Argon2.AArch64.Initial.headerWords_ok s 6 (by decide) h.left.space, VG.Proof.Argon2.AArch64.Initial.headerWords_ok t 6 (by decide) h.right.space⟩)
  exact ct.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, hp, ⟨_, ka⟩, ⟨_, kb⟩⟩ => hp.keeps ka kb)

theorem fixed_header_rel (v : HPrime.Backend) :
    RelCT isa VG.Proof.Argon2.AArch64.Initial.Related (Impl.Argon2.AArch64.HPrime.absorbFixed v.hash 768 24) VG.Proof.Argon2.AArch64.Initial.Related := by
  have args := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.AArch64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block (Impl.Argon2.AArch64.HPrime.fixedArgs 768 24)) (by taint_decide)).wpDep
    (fun s t _ => ⟨HPrime.fixedArgs_ok s 768 24 (by decide) (by decide),
      HPrime.fixedArgs_ok t 768 24 (by decide) (by decide)⟩)
  have call := HPrime.update_rel v (P := fun a b => True ∧ ∃ s t, VG.Proof.Argon2.AArch64.Initial.Related s t ∧
      HPrime.FixedArgs s a 768 24 ∧ HPrime.FixedArgs t b 768 24)
    (fun a b ⟨_, s, t, hp, ha, hb⟩ => ⟨HPrime.fixed_ready (VG.Proof.Argon2.AArch64.Initial.finalize_ready hp.left) ha (by decide) (by decide),
      HPrime.fixed_ready (VG.Proof.Argon2.AArch64.Initial.finalize_ready hp.right) hb (by decide) (by decide),
      by rw [ha.keeps.x24, hb.keeps.x24, hp.bx], by rw [ha.count, hb.count],
      by rw [ha.data, hb.data, hp.bx], by rw [ha.size, hb.size], by rw [ha.keeps.sp, hb.keeps.sp, hp.sp]⟩)
  have ct := args.seq call
  have result := VG.Proof.Argon2.AArch64.Initial.hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h, by simp⟩)
    (fun s t h => ⟨HPrime.absorbFixed_keeps v s 768 24 (VG.Proof.Argon2.AArch64.Initial.finalize_ready h.left) (by decide) (by decide) (by decide),
      HPrime.absorbFixed_keeps v t 768 24 (VG.Proof.Argon2.AArch64.Initial.finalize_ready h.right) (by decide) (by decide) (by decide)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem initialCount_rel : RelCT isa VG.Proof.Argon2.AArch64.Initial.Related (.block ([Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten)) (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.AArch64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.AArch64.Initial.initialCount_ok s, VG.Proof.Argon2.AArch64.Initial.initialCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  refine ⟨hp.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact la.trans lb.symm

theorem start_rel (v : HPrime.Backend) :
    RelCT isa VG.Proof.Argon2.AArch64.Initial.Related (start v.hash) (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) :=
  digestLength_rel.seq ((VG.Proof.Argon2.AArch64.Initial.init_hash_rel v).seq (header_state_rel.seq
    ((VG.Proof.Argon2.AArch64.Initial.fixed_header_rel v).seq VG.Proof.Argon2.AArch64.Initial.initialCount_rel)))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialFinishCT`. -/
section
/-! H₀ finalization and its fixed-size digest copy reveal no input contents. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem finishCount_rel : RelCT isa (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) (.block ([Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten))
    (fun s t => VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.1.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.AArch64.Initial.finishCount_ok s, VG.Proof.Argon2.AArch64.Initial.finishCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨⟨hp.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [ka.regs .x20 (by decide) (by decide), kb.regs .x20 (by decide) (by decide)]
    exact hp.2 _ (by simp)
  · rw [ca, cb]; exact hp.2 _ (by simp)

theorem finalize_hash_rel (v : HPrime.Backend) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1)
      (Impl.Argon2.AArch64.HPrime.finalize v.hash) VG.Proof.Argon2.AArch64.Initial.Related := by
  have ct := HPrime.finalize_rel v (P := fun s t => VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1)
    (fun s t h => ⟨VG.Proof.Argon2.AArch64.Initial.finalize_ready h.1.1.left, VG.Proof.Argon2.AArch64.Initial.finalize_ready h.1.1.right, h.1.1.bx, h.2, h.1.1.sp⟩)
  have result := VG.Proof.Argon2.AArch64.Initial.hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1.1, by simp⟩)
    (fun s t h => ⟨HPrime.finalize_keeps v s (VG.Proof.Argon2.AArch64.Initial.finalize_ready h.1.1.left),
      HPrime.finalize_keeps v t (VG.Proof.Argon2.AArch64.Initial.finalize_ready h.1.1.right)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem finishOutput_rel : RelCT isa VG.Proof.Argon2.AArch64.Initial.Related
    (.block ([Impl.Argon2.AArch64.Instructions.mov .x22 .x19, Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten))
      (HPrime.AgreeRegs [.x24, .x22, .x8]) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.AArch64.Initial.Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.mov .x22 .x19, Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.AArch64.Initial.finishOutput_ok s, VG.Proof.Argon2.AArch64.Initial.finishOutput_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨da, la, _, ka⟩, ⟨db, lb, _, kb⟩⟩
  refine ⟨by rw [ka.sp, kb.sp, hp.sp], ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ka.x24, kb.x24, hp.bx]
  · rw [da, db, hp.bp]
  · rw [la, lb]

theorem copy_digest_rel : RelCT isa (HPrime.AgreeRegs [.x24, .x22, .x8])
    Impl.Argon2.AArch64.HPrime.copy (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x24, .x22, .x8])
    (fun _ _ h => h.taint) (by taint_decide)

theorem finish_rel (v : HPrime.Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) (VG.Impl.Argon2.AArch64.Initial.finish v.hash) (fun _ _ => True) :=
  finishCount_rel.seq ((VG.Proof.Argon2.AArch64.Initial.finalize_hash_rel v).seq (finishOutput_rel.seq VG.Proof.Argon2.AArch64.Initial.copy_digest_rel))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialAbsorbCT`. -/
section
/-! H₀ updates depend on public lengths and pointers, never on input contents. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

def PrefixRelated (lo : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20] s t ∧ LengthArgs s lo a ∧ LengthArgs t lo b

theorem prefix_rel (v : HPrime.Backend) (lo : Nat) (slot : lo ∈ VG.Proof.Argon2.AArch64.Initial.slots)
    (bound : lo + 8 ≤ 272)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24]) (.block (lengthArgs lo)) hint).isSome = true) :
    RelCT isa (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20])
      (.seq (.block (lengthArgs lo)) (Impl.Argon2.AArch64.HPrime.update v.hash)) (VG.Proof.Argon2.AArch64.Initial.LengthRelated lo) := by
  have args := ((VG.Proof.Argon2.AArch64.Initial.lengthArgs_rel lo check).mono (P' := VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20])
    (fun _ _ h => ⟨h.1.sp, h.1.bp, h.1.bx⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨lengthArgs_ok s lo (VG.Proof.Argon2.AArch64.Initial.slots_aligned lo slot) (by omega) (h.1.left.space.readable lo slot)
      (by simpa using h.1.left.space.write 792 4 (by decide)),
      lengthArgs_ok t lo (VG.Proof.Argon2.AArch64.Initial.slots_aligned lo slot) (by omega) (h.1.right.space.readable lo slot)
      (by simpa using h.1.right.space.write 792 4 (by decide))⟩)
  have call := HPrime.update_rel v (P := VG.Proof.Argon2.AArch64.Initial.PrefixRelated lo) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨VG.Proof.Argon2.AArch64.Initial.prefix_update_ready hp.1.left.space ha, VG.Proof.Argon2.AArch64.Initial.prefix_update_ready hp.1.right.space hb,
      by rw [ha.keeps.x24, hb.keeps.x24, hp.1.bx], by rw [ha.count, hb.count]; exact hp.2 _ (by simp),
      by rw [ha.pointer, hb.pointer, hp.1.bx], by rw [ha.size, hb.size],
      by rw [ha.keeps.sp, hb.keeps.sp, hp.1.sp]⟩)
  have called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (VG.Proof.Argon2.AArch64.Initial.prefix_update_ready hp.1.left.space ha),
      HPrime.update_keeps v b (VG.Proof.Argon2.AArch64.Initial.prefix_update_ready hp.1.right.space hb)⟩)
  have finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    have rel := hp.1.keeps ha.keeps hb.keeps
    have prepared : VG.Proof.Argon2.AArch64.Initial.LengthRelated lo x y := by
      refine ⟨⟨rel, ?_⟩, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.other _ (by decide),
            hb.other _ (by decide)]
          exact hp.2 _ (by simp)
        · rw [ha.length, hb.length]; exact hp.1.words lo slot
      · rw [hp.1.left.space.word_keeps ha.keeps lo bound]; exact ha.length
      · rw [hp.1.right.space.word_keeps hb.keeps lo bound]; exact hb.length
    exact prepared.hash_keeps bound ka kb)
  exact args.seq finished

def InputRelated (lo po : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, VG.Proof.Argon2.AArch64.Initial.LengthRelated lo s t ∧ InputArgs s a po ∧ InputArgs t b po

theorem input_rel (v : HPrime.Backend) (po lo : Nat) (input : (po, lo) ∈ VG.Proof.Argon2.AArch64.Initial.inputs)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.x19]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (VG.Proof.Argon2.AArch64.Initial.LengthRelated lo)
      (.seq (.block (inputArgs po)) (Impl.Argon2.AArch64.HPrime.update v.hash)) (VG.Proof.Argon2.AArch64.Initial.LengthRelated lo) := by
  have args := ((VG.Proof.Argon2.AArch64.Initial.inputArgs_rel po check).mono (P' := VG.Proof.Argon2.AArch64.Initial.LengthRelated lo)
    (fun _ _ h => ⟨h.related.1.sp, h.related.1.bp⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨inputArgs_ok s po (VG.Proof.Argon2.AArch64.Initial.slots_aligned po (h.related.1.left.inputs _ input).pointerSlot) (by have := (h.related.1.left.inputs _ input).pointerBound; omega) (h.related.1.left.space.readable po (h.related.1.left.inputs _ input).pointerSlot),
      inputArgs_ok t po (VG.Proof.Argon2.AArch64.Initial.slots_aligned po (h.related.1.right.inputs _ input).pointerSlot) (by have := (h.related.1.right.inputs _ input).pointerBound; omega) (h.related.1.right.space.readable po (h.related.1.right.inputs _ input).pointerSlot)⟩)
  have call := HPrime.update_rel v (P := VG.Proof.Argon2.AArch64.Initial.InputRelated lo po) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨VG.Proof.Argon2.AArch64.Initial.input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha,
      VG.Proof.Argon2.AArch64.Initial.input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb,
      by rw [ha.keeps.x24, hb.keeps.x24, hp.related.1.bx],
      by rw [ha.count, hb.count, hp.related.2 .x20 (by simp)],
      by rw [ha.pointer, hb.pointer]; exact hp.related.1.words po (hp.related.1.left.inputs _ input).pointerSlot,
      by rw [ha.length, hb.length]; exact hp.related.2 .x22 (by simp),
      by rw [ha.keeps.sp, hb.keeps.sp, hp.related.1.sp]⟩)
  have called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (VG.Proof.Argon2.AArch64.Initial.input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha),
      HPrime.update_keeps v b (VG.Proof.Argon2.AArch64.Initial.input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb)⟩)
  have finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    have left := hp.related.1.left.inputs _ input
    have right := hp.related.1.right.inputs _ input
    have prepared : VG.Proof.Argon2.AArch64.Initial.LengthRelated lo x y := by
      refine ⟨⟨hp.related.1.keeps ha.keeps hb.keeps, ?_⟩, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.total, hb.total, hp.related.2 .x20 (by simp)]
        · rw [ha.other _ (by decide),
            hb.other _ (by decide)]
          exact hp.related.2 .x22 (by simp)
      · rw [left.space.word_keeps ha.keeps lo left.lengthBound,
          ha.other _ (by decide)]
        exact hp.leftLength
      · rw [right.space.word_keeps hb.keeps lo right.lengthBound,
          hb.other _ (by decide)]
        exact hp.rightLength
    exact prepared.hash_keeps left.lengthBound ka kb)
  exact args.seq finished

theorem addCount_rel (lo : Nat) :
    RelCT isa (VG.Proof.Argon2.AArch64.Initial.LengthRelated lo) (.block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.AArch64.Initial.LengthRelated lo) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.related.1.sp, by simp [Taint.ofRegs]⟩)
    (c := .block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) (by taint_decide)).wpDep
    (fun s t _ => ⟨VG.Proof.Argon2.AArch64.Initial.addCount_ok s, VG.Proof.Argon2.AArch64.Initial.addCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨hp.related.1.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  rw [ca, cb, hp.related.2 .x20 (by simp), hp.related.2 .x22 (by simp)]

theorem absorb_rel (v : HPrime.Backend) (po lo : Nat) (input : (po, lo) ∈ VG.Proof.Argon2.AArch64.Initial.inputs)
    (lengthCheck : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24]) (.block (lengthArgs lo)) hint).isSome = true)
    (pointerCheck : ∃ hint, (taint.check (Taint.ofRegs [.x19]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) (absorb v.hash po lo) (VG.Proof.Argon2.AArch64.Initial.RelatedRegs [.x20]) := by
  have slot : lo ∈ VG.Proof.Argon2.AArch64.Initial.slots := by
    have all : ∀ p ∈ VG.Proof.Argon2.AArch64.Initial.inputs, p.2 ∈ VG.Proof.Argon2.AArch64.Initial.slots := by decide
    exact all _ input
  have bound : lo + 8 ≤ 272 := by
    have all : ∀ d ∈ VG.Proof.Argon2.AArch64.Initial.slots, d + 8 ≤ 272 := by decide
    exact all lo slot
  exact ((VG.Proof.Argon2.AArch64.Initial.prefix_rel v lo slot bound lengthCheck).seq
    (((VG.Proof.Argon2.AArch64.Initial.input_rel v po lo input pointerCheck).seq (VG.Proof.Argon2.AArch64.Initial.addCount_rel lo)).assoc)).assoc

end VG.Proof.Argon2.AArch64.Initial
end

/-! Complete H₀ is constant time for every verified BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem code_rel (v : HPrime.Backend) :
    RelCT isa VG.Proof.Argon2.AArch64.Initial.Related (VG.Impl.Argon2.AArch64.Initial.code v.hash) (fun _ _ => True) :=
  (VG.Proof.Argon2.AArch64.Initial.start_rel v).seq
    ((VG.Proof.Argon2.AArch64.Initial.absorb_rel v passwordOffset passwordLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((VG.Proof.Argon2.AArch64.Initial.absorb_rel v saltOffset saltLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((VG.Proof.Argon2.AArch64.Initial.absorb_rel v secretOffset secretLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((VG.Proof.Argon2.AArch64.Initial.absorb_rel v adOffset adLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
      (VG.Proof.Argon2.AArch64.Initial.finish_rel v)))))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialBodyReviewedCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitFillCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinishStageCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalOutputCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalCallCT`. -/
section
/-! # The final H′ call leak only their public argument registers -/

namespace VG.Proof.Argon2.AArch64.FinalCall

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)

theorem hPrime_call_rel (v : HPrime.Backend) (name : String) (len : Nat)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → VG.Proof.Argon2.AArch64.FinalCall.CallReady len s ∧ VG.Proof.Argon2.AArch64.FinalCall.CallReady len t ∧
      s.gpr .x1 = 1024 ∧ t.gpr .x1 = 1024 ∧ s.gpr .x3 = BitVec.ofNat 64 len ∧ t.gpr .x3 = BitVec.ofNat 64 len ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x2 = t.gpr .x2 ∧
      s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp) :
    RelCT isa P (.call name (VG.Impl.Argon2.AArch64.HPrime.code v.hash)) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, x4, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := VG.Proof.Argon2.AArch64.FinalCall.hPrime_call_hyps len s hs ls os
  obtain ⟨pt, ct, wt⟩ := VG.Proof.Argon2.AArch64.FinalCall.hPrime_call_hyps len t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧
    s.callEntry.gpr .x4 = t.callEntry.gpr .x4 ∧
    s.callEntry.sp = t.callEntry.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, x4, sp⟩

end VG.Proof.Argon2.AArch64.FinalCall
end

/-! Final hashing exposes only the public tag length and pointers, for any hash backend. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FinalOutput.Ready p s
  right : VG.Proof.Argon2.AArch64.FinalOutput.Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : VG.Proof.Argon2.AArch64.FinalOutput.output s = VG.Proof.Argon2.AArch64.FinalOutput.output t
  works : VG.Proof.Argon2.AArch64.FinalOutput.work s = VG.Proof.Argon2.AArch64.FinalOutput.work t

structure NextRelated (p : Params) (s t : State) : Prop where
  left : FinalCall.CallReady p.tagLen s
  right : FinalCall.CallReady p.tagLen t
  leftInputLength : s.gpr .x1 = 1024
  rightInputLength : t.gpr .x1 = 1024
  leftOutputLength : s.gpr .x3 = BitVec.ofNat 64 p.tagLen
  rightOutputLength : t.gpr .x3 = BitVec.ofNat 64 p.tagLen
  inputs : s.gpr .x0 = t.gpr .x0
  outputs : s.gpr .x2 = t.gpr .x2
  works : s.gpr .x4 = t.gpr .x4
  stacks : s.sp = t.sp

theorem args_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem args_rel (p : Params) : RelCT isa (VG.Proof.Argon2.AArch64.FinalOutput.Related p)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (VG.Proof.Argon2.AArch64.FinalOutput.NextRelated p) := by
  have trace := args_trace.mono (P' := VG.Proof.Argon2.AArch64.FinalOutput.Related p) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.FinalOutput.args_ok s h.left.reads, VG.Proof.Argon2.AArch64.FinalOutput.args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.keeps.sp).trans (hp.stacks.trans (hb.keeps.sp).symm)⟩

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.AArch64.FinalOutput.Related p) (Impl.Argon2.AArch64.FinalOutput.code name v.hash) (fun _ _ => True) :=
  (VG.Proof.Argon2.AArch64.FinalOutput.args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! Complete finalization has a public trace for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.Finish.Ready p s
  right : VG.Proof.Argon2.AArch64.Finish.Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : VG.Proof.Argon2.AArch64.ReductionState.matrix s = VG.Proof.Argon2.AArch64.ReductionState.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix t) p.blocks rightMemory

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftMemory rightMemory : Array Block) :
    RelCT isa (VG.Proof.Argon2.AArch64.Finish.Related p leftMemory rightMemory) (Impl.Argon2.AArch64.Finish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq reduceA outputA =>
    cases eb with
    | seq reduceB outputB =>
      have related : ReductionInit.Related p leftMemory rightMemory s t :=
        ⟨hp.left.reduction, hp.right.reduction, hp.bases, hp.stacks, hp.matrices, hp.leftMatrix, hp.rightMatrix⟩
      obtain ⟨reduceTrace, _⟩ := FinalReduction.code_rel p hp.left.reduction.allocation.positive
        leftMemory rightMemory _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, doneA⟩ := FinalReduction.code_ok s p hp.left.reduction leftMemory hp.leftMatrix
      obtain ⟨_, sb, runB, doneB⟩ := FinalReduction.code_ok t p hp.right.reduction rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have finalRelated : FinalOutput.Related p _ _ :=
        ⟨VG.Proof.Argon2.AArch64.Finish.output_ready hp.left doneA, VG.Proof.Argon2.AArch64.Finish.output_ready hp.right doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.base.trans (hp.matrices.trans doneB.base.symm),
          (VG.Proof.Argon2.AArch64.Finish.frame_word hp.left.reduction doneA 256 (by decide)).trans
            (hp.outputs.trans (VG.Proof.Argon2.AArch64.Finish.frame_word hp.right.reduction doneB 256 (by decide)).symm),
          (VG.Proof.Argon2.AArch64.Finish.frame_word hp.left.reduction doneA 248 (by decide)).trans
            (hp.works.trans (VG.Proof.Argon2.AArch64.Finish.frame_word hp.right.reduction doneB 248 (by decide)).symm)⟩
      obtain ⟨outputTrace, _⟩ := FinalOutput.code_rel v name p _ _ _ _ _ _ finalRelated outputA outputB
      exact ⟨by rw [reduceTrace, outputTrace], trivial⟩

end VG.Proof.Argon2.AArch64.Finish
end

/-! Merged from `Proof.Argon2.AArch64.FillSlicesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSlicesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSliceCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillLanesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillLanesBodyCT`. -/
section
/-! Lane iteration preserves public allocations and loops on the public lane count. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillLanes

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (SegmentSetup.Related p pass lane slice leftState rightState) VG.Impl.Argon2.AArch64.FillLanes.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (lane + 1 < p.lanes → VG.Proof.Argon2.AArch64.FillLanes.NextRelated p pass (lane + 1) slice
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := SegmentSetup.code_rel p pass lane slice leftState rightState
        _ _ _ _ _ _ hp segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := SegmentSetup.code_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := SegmentSetup.code_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      have bases := (filledA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.ready.bases.trans (filledB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)
      have stacks := filledA.sp.trans (hp.ready.stacks.trans filledB.sp.symm)
      obtain ⟨advancedTrace, _⟩ := VG.Proof.Argon2.AArch64.FillLanes.advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.AArch64.FillLanes.body_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.AArch64.FillLanes.body_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.ready.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.ready.work.trans doneB.work.symm)⟩, doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)).trans
          (hp.ready.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.ready.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillLanes
end

/-! The lane loop exposes only the slice's specified reference log. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice lane count leftState).indices =
    (Proof.Argon2.lanes p pass slice lane count rightState).indices

theorem loop_rel (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillLanes.Related p pass lane slice count leftState rightState) Impl.Argon2.AArch64.FillLanes.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftState rightState : FillState),
    lane + n = p.lanes ∧ 0 < n ∧ VG.Proof.Argon2.AArch64.FillLanes.Related p pass lane slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have segmentRelated : SegmentSetup.Related p pass j slice ls rs s t :=
        ⟨hp.ready, hp.leftMatrix, hp.rightMatrix, Proof.Argon2.lanes_first_segment p pass slice j n ls rs
          hp.ready.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.AArch64.FillLanes.body_rel p pass j slice ls rs _ _ _ _ _ _ segmentRelated ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.AArch64.FillLanes.body_ok s p pass j slice hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨ready, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.segment p pass j slice 0 p.segmentLen ls,
          Proof.Argon2.segment p pass j slice 0 p.segmentLen rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftState, rightState, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillLanes
end

/-! A complete slice exposes only its specified reference log. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FillSlice.Ready p pass slice s
  right : VG.Proof.Argon2.AArch64.FillSlice.Ready p pass slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice 0 p.lanes leftState).indices =
    (Proof.Argon2.lanes p pass slice 0 p.lanes rightState).indices

theorem setup_trace : RelCT isa (fun s t : State => s.sp = t.sp) (.block Impl.Argon2.AArch64.FillSlice.setup) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setup_public_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillSlice.Related p pass slice leftState rightState) (.block Impl.Argon2.AArch64.FillSlice.setup)
      (FillLanes.Related p pass 0 slice p.lanes leftState rightState) := by
  have trace := setup_trace.mono (P' := VG.Proof.Argon2.AArch64.FillSlice.Related p pass slice leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.FillSlice.setup_ok s p pass slice h.left, VG.Proof.Argon2.AArch64.FillSlice.setup_ok t p pass slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_⟩, ?_, ?_, hp.indices⟩
  · rw [ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.bases
  · rw [ha.keeps.sp, hb.keeps.sp]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .x19 (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .x19 (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillSlice.Related p pass slice leftState rightState) Impl.Argon2.AArch64.FillSlice.code (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA lanesA =>
    cases eb with
    | seq setupB lanesB =>
      obtain ⟨setupTrace, related⟩ := VG.Proof.Argon2.AArch64.FillSlice.setup_public_rel p pass slice leftState rightState _ _ _ _ _ _ hp setupA setupB
      obtain ⟨lanesTrace, _⟩ := FillLanes.loop_rel p pass 0 slice p.lanes leftState rightState
        hp.left.parameters.lanesPositive (by omega) _ _ _ _ _ _ related lanesA lanesB
      exact ⟨by rw [setupTrace, lanesTrace], trivial⟩

end VG.Proof.Argon2.AArch64.FillSlice
end

/-! A slice iteration preserves public allocations and its public continuation guard. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_rel : RelCT isa (fun s t : State => s.sp = t.sp)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : FillSlice.Ready p pass slice s
  right : FillSlice.Ready p pass slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (FillSlice.Related p pass slice leftState rightState) VG.Impl.Argon2.AArch64.FillSlices.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (slice + 1 < 4 → VG.Proof.Argon2.AArch64.FillSlices.NextRelated p pass (slice + 1)
        (Proof.Argon2.lanes p pass slice 0 p.lanes leftState) (Proof.Argon2.lanes p pass slice 0 p.lanes rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq sliceA advanceA =>
    cases eb with
    | seq sliceB advanceB =>
      obtain ⟨sliceTrace, _⟩ := FillSlice.code_rel p pass slice leftState rightState _ _ _ _ _ _ hp sliceA sliceB
      obtain ⟨_, sa, fillRunA, filledA⟩ := FillSlice.code_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, sb, fillRunB, filledB⟩ := FillSlice.code_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det sliceA fillRunA
      obtain ⟨_, rfl⟩ := Exec.det sliceB fillRunB
      have stacks := filledA.sp.trans (hp.stacks.trans filledB.sp.symm)
      obtain ⟨advanceTrace, _⟩ := VG.Proof.Argon2.AArch64.FillSlices.advance_rel _ _ _ _ _ _ stacks advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.AArch64.FillSlices.body_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.AArch64.FillSlices.body_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceB advanceB) runB
      refine ⟨by rw [sliceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! The complete pass leaks only its reviewed reference log, including Argon2id's mode change. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice count : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  states : VG.Proof.Argon2.AArch64.FillSlices.NextRelated p pass slice leftState rightState s t
  indices : (Proof.Argon2.slices p pass slice count leftState).indices =
    (Proof.Argon2.slices p pass slice count rightState).indices

theorem loop_rel (p : Params) (pass slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillSlices.Related p pass slice count leftState rightState) Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (slice : Nat) (leftState rightState : FillState),
    slice + n = 4 ∧ 0 < n ∧ VG.Proof.Argon2.AArch64.FillSlices.Related p pass slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillSlices.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endSlice, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have sliceRelated : FillSlice.Related p pass j ls rs s t :=
        ⟨hp.states.left, hp.states.right, hp.states.bases, hp.states.stacks, hp.states.matrices, hp.states.work,
          hp.states.leftMatrix, hp.states.rightMatrix, Proof.Argon2.slices_first_lane_fold p pass j n ls rs
            hp.states.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.AArch64.FillSlices.body_rel p pass j ls rs _ _ _ _ _ _ sliceRelated ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.AArch64.FillSlices.body_ok s p pass j hp.states.left ls hp.states.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < 4 := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have indices := hp.indices
        rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.lanes p pass j 0 p.lanes ls,
          Proof.Argon2.lanes p pass j 0 p.lanes rs, by omega, by omega, next active, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨slice, leftState, rightState, endSlice, positive, h⟩) (fun _ _ h => h)

theorem pass_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.FillSlices.NextRelated p pass 0 leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices)
      Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  refine (VG.Proof.Argon2.AArch64.FillSlices.loop_rel p pass 0 4 leftState rightState (by decide) (by decide)).mono ?_ (fun _ _ h => h)
  intro s t h
  refine ⟨h.1, ?_⟩
  rw [Proof.Argon2.slices_pass p pass leftState, Proof.Argon2.slices_pass p pass rightState]
  exact h.2

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! Merged from `Proof.Argon2.AArch64.FillIterationsCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillIterationsBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillIterationCT`. -/
section
/-! Pass setup retains public pointers and exposes only the reviewed pass log. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FillIteration.Ready p pass s
  right : VG.Proof.Argon2.AArch64.FillIteration.Ready p pass t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (fillPass p leftState pass).indices = (fillPass p rightState pass).indices

theorem setup_trace : RelCT isa (fun s t : State => s.sp = t.sp) (.block Impl.Argon2.AArch64.FillIteration.setup) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setup_public_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillIteration.Related p pass leftState rightState) (.block Impl.Argon2.AArch64.FillIteration.setup)
      (fun s t => FillSlices.NextRelated p pass 0 leftState rightState s t ∧
        (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) := by
  have trace := setup_trace.mono (P' := VG.Proof.Argon2.AArch64.FillIteration.Related p pass leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨VG.Proof.Argon2.AArch64.FillIteration.setup_ok s p pass h.left, VG.Proof.Argon2.AArch64.FillIteration.setup_ok t p pass h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_, ?_, ?_⟩, hp.indices⟩
  · rw [ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.bases
  · rw [ha.keeps.sp, hb.keeps.sp]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .x19 (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .x19 (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillIteration.Related p pass leftState rightState) Impl.Argon2.AArch64.FillIteration.code (fun _ _ => True) :=
  (VG.Proof.Argon2.AArch64.FillIteration.setup_public_rel p pass leftState rightState).seq (FillSlices.pass_rel p pass leftState rightState)

end VG.Proof.Argon2.AArch64.FillIteration
end

/-! Iteration advances its public pass counter and retains the reviewed filling log. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    advance (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FillIterations.Ready p pass s
  right : VG.Proof.Argon2.AArch64.FillIterations.Ready p pass t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => VG.Proof.Argon2.AArch64.FillIterations.NextRelated p pass leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) VG.Impl.Argon2.AArch64.FillIterations.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (pass + 1 < p.passes → VG.Proof.Argon2.AArch64.FillIterations.NextRelated p (pass + 1)
        (fillPass p leftState pass)
        (fillPass p rightState pass) s t)) := by
  intro s t ts tt a b hp ea eb
  obtain ⟨hp, indices⟩ := hp
  have related : FillIteration.Related p pass leftState rightState s t :=
    ⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.work, hp.leftMatrix, hp.rightMatrix, indices⟩
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := FillIteration.code_rel p pass leftState rightState
        _ _ _ _ _ _ related segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := FillIteration.code_ok s p pass hp.left.filling leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillIteration.code_ok t p pass hp.right.filling rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      have bases := (filledA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
        (hp.bases.trans (filledB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      have stacks := filledA.sp.trans (hp.stacks.trans filledB.sp.symm)
      obtain ⟨advancedTrace, _⟩ := VG.Proof.Argon2.AArch64.FillIterations.advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := VG.Proof.Argon2.AArch64.FillIterations.body_ok s p pass hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := VG.Proof.Argon2.AArch64.FillIterations.body_ok t p pass hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! The pass loop exposes only the complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : VG.Proof.Argon2.AArch64.FillIterations.NextRelated p pass leftState rightState s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p pass count leftState).indices =
    (Proof.Argon2.iterations p pass count rightState).indices

theorem loop_rel (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillIterations.Related p pass count leftState rightState) Impl.Argon2.AArch64.FillIterations.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (pass : Nat) (leftState rightState : FillState),
    pass + n = p.passes ∧ 0 < n ∧ VG.Proof.Argon2.AArch64.FillIterations.Related p pass n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillIterations.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endPass, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have passIndices := Proof.Argon2.iterations_first_pass p j n ls rs
        hp.ready.left.filling.parameters.segment_bound.1 hp.indices
      obtain ⟨trace, flags, next⟩ := VG.Proof.Argon2.AArch64.FillIterations.body_rel p j ls rs _ _ _ _ _ _ ⟨hp.ready, passIndices⟩ ea eb
      obtain ⟨_, a', runA, done⟩ := VG.Proof.Argon2.AArch64.FillIterations.body_ok s p j hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.passes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have ready := next active
        have indices := hp.indices
        rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at indices
        exact ⟨n, by omega, j + 1, fillPass p ls j,
          fillPass p rs j, by omega, by omega, ready, ready.leftMatrix, ready.rightMatrix, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨pass, leftState, rightState, endPass, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! Merged from `Proof.Argon2.AArch64.FillFinishCT`. -/
section
/-! Filling and finalization expose only the reviewed filling reference log. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftState rightState : FillState) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.FillFinish.Ready p s
  right : VG.Proof.Argon2.AArch64.FillFinish.Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : VG.Proof.Argon2.AArch64.ReductionState.matrix s = VG.Proof.Argon2.AArch64.ReductionState.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (VG.Proof.Argon2.AArch64.ReductionState.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p 0 p.passes leftState).indices =
    (Proof.Argon2.iterations p 0 p.passes rightState).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftState rightState : FillState) :
    RelCT isa (VG.Proof.Argon2.AArch64.FillFinish.Related p leftState rightState) (Impl.Argon2.AArch64.FillFinish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA finishA =>
    cases eb with
    | seq fillB finishB =>
      have related : FillIterations.Related p 0 p.passes leftState rightState s t :=
        ⟨⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.works, hp.leftMatrix, hp.rightMatrix⟩,
          hp.leftMatrix, hp.rightMatrix, hp.indices⟩
      obtain ⟨fillTrace, _⟩ := FillIterations.loop_rel p 0 p.passes leftState rightState hp.left.positive
        (Nat.zero_add _) _ _ _ _ _ _ related fillA fillB
      obtain ⟨_, sa, runA, doneA⟩ := FillIterations.loop_ok p.passes s p 0 hp.left.filling leftState
        hp.leftMatrix hp.left.positive (Nat.zero_add _)
      obtain ⟨_, sb, runB, doneB⟩ := FillIterations.loop_ok p.passes t p 0 hp.right.filling rightState
        hp.rightMatrix hp.right.positive (Nat.zero_add _)
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      have finalRelated : Finish.Related p (Proof.Argon2.iterations p 0 p.passes leftState).memory
          (Proof.Argon2.iterations p 0 p.passes rightState).memory _ _ :=
        ⟨VG.Proof.Argon2.AArch64.FillFinish.finish_ready hp.left.filling hp.left.finish doneA, VG.Proof.Argon2.AArch64.FillFinish.finish_ready hp.right.filling hp.right.finish doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
          (doneA.frame_word hp.left.filling 256 (by decide) (by decide)).trans
            (hp.outputs.trans (doneB.frame_word hp.right.filling 256 (by decide) (by decide)).symm),
          (doneA.frame_word hp.left.filling 248 (by decide) (by decide)).trans
            (hp.works.trans (doneB.frame_word hp.right.filling 248 (by decide) (by decide)).symm),
          doneA.represented, doneB.represented⟩
      obtain ⟨finishTrace, _⟩ := Finish.code_rel v name p _ _ _ _ _ _ _ _ finalRelated finishA finishB
      exact ⟨by rw [fillTrace, finishTrace], trivial⟩

end VG.Proof.Argon2.AArch64.FillFinish
end

/-! The entire post-H₀ pipeline leaks only the reviewed complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (bytesAt s.mem (s.gpr .x19) 64)

structure Related (p : Params) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.InitFill.Ready p s
  right : VG.Proof.Argon2.AArch64.InitFill.Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.AArch64.InitFill.initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.AArch64.InitFill.initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.AArch64.InitFill.Related p) (Impl.Argon2.AArch64.InitFill.code name v.hash) (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  have params := hp.left.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans params.lanesBound (by decide)
  have pub : MemoryInit.AgreeBases s t := by
    refine ⟨hp.stacks, ?_⟩
    intro r hr
    simp only [MemoryInit.publicBases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.bases
    · exact hp.left.scratch.trans (hp.works.trans hp.right.scratch.symm)
    · exact hp.left.initializing.laneLength.trans hp.right.initializing.laneLength.symm
  have rightReady : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen t := by
    rw [hp.matrices]; exact hp.right.initializing
  cases ea with
  | seq initA restA =>
    cases eb with
    | seq initB restB =>
      have initTrace := MemoryInit.code_ct v name (FillKernel.matrix s) p.lanes p.laneLen
        params.lanesPositive lanesBound q _ _ _ _ _ _ hp.left.initializing rightReady pub initA initB
      obtain ⟨_, sa, runA, doneA⟩ := MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen
        hp.left.initializing params.lanesPositive lanesBound q
      obtain ⟨_, sb, runB, doneB⟩ := MemoryInit.complete_ok v name t (FillKernel.matrix t) p.lanes p.laneLen
        hp.right.initializing params.lanesPositive lanesBound q
      obtain ⟨_, rfl⟩ := Exec.det initA runA
      obtain ⟨_, rfl⟩ := Exec.det initB runB
      cases restA with
      | seq setupA fillA =>
        cases restB with
        | seq setupB fillB =>
          have bases := doneA.bp.trans (hp.bases.trans doneB.bp.symm)
          obtain ⟨setupTrace, _⟩ := FillSetup.code_rel _ _ _ _ _ _ ⟨bases, doneA.sp.trans (hp.stacks.trans doneB.sp.symm)⟩ setupA setupB
          obtain ⟨_, ca, runA, preparedA⟩ := FillSetup.code_ok _ p (VG.Proof.Argon2.AArch64.InitFill.initialized_setup hp.left doneA)
          obtain ⟨_, cb, runB, preparedB⟩ := FillSetup.code_ok _ p (VG.Proof.Argon2.AArch64.InitFill.initialized_setup hp.right doneB)
          obtain ⟨_, rfl⟩ := Exec.det setupA runA
          obtain ⟨_, rfl⟩ := Exec.det setupB runB
          have preparedBases := (preparedA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).trans
            (bases.trans (preparedB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).symm)
          have preparedStacks := preparedA.sp.trans
            ((doneA.sp.trans (hp.stacks.trans doneB.sp.symm)).trans
              preparedB.sp.symm)
          have initMatrices := (doneA.frame_word hp.left.initializing.space 232 (by decide) (Or.inr (by decide))).trans
            (hp.matrices.trans (doneB.frame_word hp.right.initializing.space 232 (by decide) (Or.inr (by decide))).symm)
          have matrices := preparedA.matrix.trans (initMatrices.trans preparedB.matrix.symm)
          have initOutputs := (doneA.frame_word hp.left.initializing.space 256 (by decide) (Or.inr (by decide))).trans
            (hp.outputs.trans (doneB.frame_word hp.right.initializing.space 256 (by decide) (Or.inr (by decide))).symm)
          have outputs := (preparedA.words 256 (by decide) (by decide)).trans
            (initOutputs.trans (preparedB.words 256 (by decide) (by decide)).symm)
          have initWorks := (doneA.frame_word hp.left.initializing.space 248 (by decide) (Or.inr (by decide))).trans
            (hp.works.trans (doneB.frame_word hp.right.initializing.space 248 (by decide) (Or.inr (by decide))).symm)
          have works := (preparedA.words 248 (by decide) (by decide)).trans
            (initWorks.trans (preparedB.words 248 (by decide) (by decide)).symm)
          have related : FillFinish.Related p (VG.Proof.Argon2.AArch64.InitFill.initial p s) (VG.Proof.Argon2.AArch64.InitFill.initial p t) _ _ :=
            ⟨preparedA.finish_ready (VG.Proof.Argon2.AArch64.InitFill.initialized_setup hp.left doneA) (VG.Proof.Argon2.AArch64.InitFill.initialized_output hp.left doneA) hp.left.positive,
              preparedB.finish_ready (VG.Proof.Argon2.AArch64.InitFill.initialized_setup hp.right doneB) (VG.Proof.Argon2.AArch64.InitFill.initialized_output hp.right doneB) hp.right.positive,
              preparedBases, preparedStacks, matrices, outputs, works,
              preparedA.represents (VG.Proof.Argon2.AArch64.InitFill.initialized_setup hp.left doneA) _ (VG.Proof.Argon2.AArch64.InitFill.initialized_represents hp.left doneA),
              preparedB.represents (VG.Proof.Argon2.AArch64.InitFill.initialized_setup hp.right doneB) _ (VG.Proof.Argon2.AArch64.InitFill.initialized_represents hp.right doneB), hp.indices⟩
          obtain ⟨fillTrace, _⟩ := FillFinish.code_rel v name p (VG.Proof.Argon2.AArch64.InitFill.initial p s) (VG.Proof.Argon2.AArch64.InitFill.initial p t) _ _ _ _ _ _ related fillA fillB
          exact ⟨by rw [initTrace, setupTrace, fillTrace], trivial⟩

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Complete derivation reveals only its reviewed filling reference sequence. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (initialHash p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset))

structure Related (p : Params) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.InitialBody.Ready p s
  right : VG.Proof.Argon2.AArch64.InitialBody.Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.AArch64.InitialBody.initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (VG.Proof.Argon2.AArch64.InitialBody.initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.AArch64.InitialBody.Related p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) := by
  have hashed := ((Initial.code_rel v).mono (P' := VG.Proof.Argon2.AArch64.InitialBody.Related p) (fun _ _ h => h.hashing)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Initial.initialHash_ok v s h.left.hashSpace h.left.inputs p h.left.header,
        Initial.initialHash_ok v t h.right.hashSpace h.right.inputs p h.right.header⟩)
  refine hashed.seq ((InitFill.code_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, hp, ⟨da, ha⟩, ⟨db, hb⟩⟩
  have baseA : FillKernel.matrix a = FillKernel.matrix s := ha.frame_word hp.left.hashSpace 232 (by decide) (by decide)
  have baseB : FillKernel.matrix b = FillKernel.matrix t := hb.frame_word hp.right.hashSpace 232 (by decide) (by decide)
  have outputA : FinalOutput.output a = FinalOutput.output s := ha.frame_word hp.left.hashSpace 256 (by decide) (by decide)
  have outputB : FinalOutput.output b = FinalOutput.output t := hb.frame_word hp.right.hashSpace 256 (by decide) (by decide)
  have workA : FinalOutput.work a = FinalOutput.work s := ha.frame_word hp.left.hashSpace 248 (by decide) (by decide)
  have workB : FinalOutput.work b = FinalOutput.work t := hb.frame_word hp.right.hashSpace 248 (by decide) (by decide)
  refine ⟨VG.Proof.Argon2.AArch64.InitialBody.hashed_ready hp.left.filling hp.left.hashSpace ha, VG.Proof.Argon2.AArch64.InitialBody.hashed_ready hp.right.filling hp.right.hashSpace hb,
    ha.x19.trans (hp.hashing.bp.trans hb.x19.symm), ha.sp.trans (hp.hashing.sp.trans hb.sp.symm),
    baseA.trans (hp.matrices.trans baseB.symm), outputA.trans (hp.outputs.trans outputB.symm),
    workA.trans (hp.works.trans workB.symm), ?_⟩
  unfold InitFill.initial
  rw [ha.x19, hb.x19, da, db]
  exact hp.indices

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! Use exactly the flattened leakage allowance of the shared derive contract. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

def references (p : Params) (s : State) : List Nat := Spec.Argon2.references p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset)

structure ReviewedRelated (p : Params) (s t : State) : Prop where
  left : VG.Proof.Argon2.AArch64.InitialBody.Ready p s
  right : VG.Proof.Argon2.AArch64.InitialBody.Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  references : VG.Proof.Argon2.AArch64.InitialBody.references p s = VG.Proof.Argon2.AArch64.InitialBody.references p t

theorem ReviewedRelated.related {p : Params} {s t : State} (h : VG.Proof.Argon2.AArch64.InitialBody.ReviewedRelated p s t) : VG.Proof.Argon2.AArch64.InitialBody.Related p s t := by
  refine ⟨h.left, h.right, h.hashing, h.matrices, h.outputs, h.works, ?_⟩
  have parameters := h.left.filling.environment.parameters
  have positive : 0 < p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p parameters.lanesPositive
    have minimum := parameters.segment_bound.1
    omega
  have indices := Proof.Argon2.references_injective p positive _ _ _ _ _ _ _ _ h.references
  unfold VG.Proof.Argon2.AArch64.InitialBody.initial
  rw [Proof.Argon2.iterations_fill, Proof.Argon2.iterations_fill]
  exact indices

theorem reviewed_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.AArch64.InitialBody.ReviewedRelated p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) :=
  (VG.Proof.Argon2.AArch64.InitialBody.code_rel v name p).mono (fun _ _ h => h.related) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! Preserve precisely the reviewed leakage relation across parameter computation. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

theorem ReviewedRelated.of_state {s₁ s₂ t₁ t₂ : State} {p : Params}
    (h : VG.Proof.Argon2.AArch64.InitialBody.ReviewedRelated p s₁ s₂) (k₁ : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s₁ t₁) (k₂ : VG.Proof.Argon2.AArch64.InitialBody.SameFrame s₂ t₂)
    (length₁ : t₁.gpr .x21 = BitVec.ofNat 64 p.laneLen)
    (length₂ : t₂.gpr .x21 = BitVec.ofNat 64 p.laneLen) : VG.Proof.Argon2.AArch64.InitialBody.ReviewedRelated p t₁ t₂ := by
  refine ⟨h.left.of_state k₁ length₁, h.right.of_state k₂ length₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨k₁.hashSpace h.hashing.left.space,
      fun input hi => k₁.input (h.hashing.left.inputs input hi)⟩,
      ⟨k₂.hashSpace h.hashing.right.space,
      fun input hi => k₂.input (h.hashing.right.inputs input hi)⟩, ?_, ?_, ?_, ?_⟩
    · rw [k₁.bp, k₂.bp]; exact h.hashing.bp
    · rw [k₁.bx, k₂.bx]; exact h.hashing.bx
    · rw [k₁.sp, k₂.sp]; exact h.hashing.sp
    · intro d hd; rw [k₁.word d, k₂.word d]; exact h.hashing.words d hd
  · unfold FillKernel.matrix; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.matrices
  · unfold FinalOutput.output; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.outputs
  · unfold FinalOutput.work; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.works
  · unfold VG.Proof.Argon2.AArch64.InitialBody.references
    rw [k₁.inputBytes passwordOffset passwordLenOffset, k₂.inputBytes passwordOffset passwordLenOffset,
      k₁.inputBytes saltOffset saltLenOffset, k₂.inputBytes saltOffset saltLenOffset,
      k₁.inputBytes secretOffset secretLenOffset, k₂.inputBytes secretOffset secretLenOffset,
      k₁.inputBytes adOffset adLenOffset, k₂.inputBytes adOffset adLenOffset]
    exact h.references

end VG.Proof.Argon2.AArch64.InitialBody

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DeriveVerified`. -/
section

section

/-! Checked literals for the entry point's fixed instruction shapes. -/

namespace VG

materialize_code Impl.Argon2.AArch64.Derive.prepare
materialize_code Impl.Argon2.AArch64.FillSetup.code
materialize_code Impl.Argon2.AArch64.FillIterations.loop
materialize_code Impl.Argon2.AArch64.FinalReduction.code

end VG

end

/-! Merged from `Proof.Argon2.AArch64.ParametersLit`. -/
section
/-! Checked literal of rounded-memory parameter computation. -/

namespace VG

materialize_code Impl.Argon2.AArch64.Parameters.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.ParametersCT`. -/
section
/-! Rounded-memory computation reads public frame addresses with a fixed trace. -/
namespace VG.Proof.Argon2.AArch64.Parameters
open VG VG.AArch64

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.Parameters.code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
end VG.Proof.Argon2.AArch64.Parameters
end

/-! Merged from `Proof.Argon2.AArch64.DeriveWords`. -/
section
/-! Exact words consumed by hashing, initialization, filling, and finalization. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Proof.Argon2.AArch64.Initial (wordAt)

theorem params_variant_code (kind passes memory lanes tagLen : Nat) (bound : kind ≤ 2) :
    (Spec.Argon2.params kind passes memory lanes tagLen).variant.code = kind := by
  by_cases zero : kind = 0
  · subst kind; rfl
  · by_cases one : kind = 1
    · subst kind; rfl
    · have two : kind = 2 := by omega
      subst kind; rfl

structure DeriveWords (s t : State) : Prop where
  passes : VG.Proof.Argon2.AArch64.Initial.wordAt t 72 = BitVec.ofNat 64 (abiParams s).passes
  saltLength : VG.Proof.Argon2.AArch64.Initial.wordAt t 80 = s.gpr .x4
  salt : VG.Proof.Argon2.AArch64.Initial.wordAt t 88 = s.gpr .x3
  passwordLength : VG.Proof.Argon2.AArch64.Initial.wordAt t 96 = s.gpr .x2
  password : VG.Proof.Argon2.AArch64.Initial.wordAt t 104 = s.gpr .x1
  kind : VG.Proof.Argon2.AArch64.Initial.wordAt t 112 = BitVec.ofNat 64 (abiParams s).variant.code
  memory : VG.Proof.Argon2.AArch64.Initial.wordAt t 176 = BitVec.ofNat 64 (abiParams s).memory
  lanes : VG.Proof.Argon2.AArch64.Initial.wordAt t 184 = BitVec.ofNat 64 (abiParams s).lanes
  secret : VG.Proof.Argon2.AArch64.Initial.wordAt t 200 = abiWord s 8
  secretLength : VG.Proof.Argon2.AArch64.Initial.wordAt t 208 = abiWord s 16
  ad : VG.Proof.Argon2.AArch64.Initial.wordAt t 216 = abiWord s 24
  adLength : VG.Proof.Argon2.AArch64.Initial.wordAt t 224 = abiWord s 32
  matrix : VG.Proof.Argon2.AArch64.Initial.wordAt t 232 = abiWord s 40
  blocks : VG.Proof.Argon2.AArch64.Initial.wordAt t 240 = BitVec.ofNat 64 (abiParams s).blocks
  work : VG.Proof.Argon2.AArch64.Initial.wordAt t 248 = abiWord s 56
  output : VG.Proof.Argon2.AArch64.Initial.wordAt t 256 = abiWord s 64
  tagLength : VG.Proof.Argon2.AArch64.Initial.wordAt t 264 = BitVec.ofNat 64 (abiParams s).tagLen

theorem private_words {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : VG.Proof.Argon2.AArch64.Derive.DeriveWords s t := by
  have parameters := private_parameters h prepared
  refine ⟨?_, private_argument_word prepared (80, .x4) (by decide),
    private_argument_word prepared (88, .x3) (by decide),
    private_argument_word prepared (96, .x2) (by decide),
    private_argument_word prepared (104, .x1) (by decide), ?_, parameters.memoryWord, parameters.lanesWord,
    private_stack_word h prepared 1 (by decide), private_stack_word h prepared 2 (by decide),
    private_stack_word h prepared 3 (by decide), private_stack_word h prepared 4 (by decide),
    private_stack_word h prepared 5 (by decide), ?_, private_stack_word h prepared 7 (by decide),
    private_stack_word h prepared 8 (by decide), ?_⟩
  · have word := private_argument_word prepared (72, .x5) (by decide)
    change VG.Proof.Argon2.AArch64.Initial.wordAt t 72 = ((s.gpr .x5).setWidth 32).setWidth 64 at word
    change VG.Proof.Argon2.AArch64.Initial.wordAt t 72 = BitVec.ofNat 64 ((s.gpr .x5).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have code := VG.Proof.Argon2.AArch64.Derive.params_variant_code ((s.gpr .x0).setWidth 32).toNat
      (abiParams s).passes (abiParams s).memory (abiParams s).lanes (abiParams s).tagLen h.kind
    change (abiParams s).variant.code = ((s.gpr .x0).setWidth 32).toNat at code
    rw [code]
    have word := private_argument_word prepared (112, .x0) (by decide)
    change VG.Proof.Argon2.AArch64.Initial.wordAt t 112 = ((s.gpr .x0).setWidth 32).setWidth 64 at word
    rw [word, BitVec.ofNat_toNat]
  · have word := private_stack_word h prepared 6 (by decide)
    change VG.Proof.Argon2.AArch64.Initial.wordAt t 240 = abiWord s 48 at word
    rw [word, ← h.blocks, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have word := private_stack_word h prepared 9 (by decide)
    change VG.Proof.Argon2.AArch64.Initial.wordAt t 264 = abiWord s 72 at word
    change VG.Proof.Argon2.AArch64.Initial.wordAt t 264 = BitVec.ofNat 64 (abiWord s 72).toNat
    rw [word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveSeparation`. -/
section
/-! Buffer separation is supplied by the shared signature, including read-only arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure AbiSeparation (s : State) : Prop where
  inputWork : ∀ r ∈ abiInputs s, r.Disjoint (abiWork s)
  matrixWork : (abiMatrix s).Disjoint (abiWork s)
  outputWork : (abiOutput s).Disjoint (abiWork s)
  matrixOutput : (abiMatrix s).Disjoint (abiOutput s)

theorem abi_separation {s : State} (h : AbiEnvironment s) : VG.Proof.Argon2.AArch64.Derive.AbiSeparation s := by
  have pairs := h.pairs
  sig_eval [abiBuffers, abiInputs, abiMatrix, abiWork, abiOutput, abiArguments] at pairs
  sig_split pairs
  constructor
  all_goals sig_eval [abiInputs, abiMatrix, abiWork, abiOutput]
  all_goals sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

theorem private_scratch {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : t.gpr .x24 = (abiWork s).base := by
  have word := prologue_word h 7 (by decide)
  change (prologueState s).mem.readW ((prologueState s).sp + 440) 64 = abiWord s 56 at word
  exact prepared.scratch.trans word

theorem abi_input_lengths {s : State} (h : AbiEnvironment s) : ∀ r ∈ abiInputs s, r.len < 2 ^ 32 := by
  have valid := h.valid
  unfold Spec.Argon2.valid at valid
  obtain ⟨_, _, _, _, _, _, _, _, password, salt, secret, ad⟩ := valid
  sig_eval [abiInputs]
  sig_and_intros
  all_goals with_reducible assumption

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveParameters`. -/
section
/-! Compute the rounded lane length before entering the complete Argon2 body. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

/-- A specification state for the body's readiness predicate, not executable code. -/
def dimensionState (s : State) (p : Params) : State :=
  s.write .x .x21 (BitVec.ofNat 64 p.laneLen)

theorem dimension_frame (s : State) (p : Params) : InitialBody.SameFrame s (VG.Proof.Argon2.AArch64.Derive.dimensionState s p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RegUpd.gpr_write_of_ne s .x _ (by decide)
  · exact RegUpd.gpr_write_of_ne s .x _ (by decide)
  · rfl
  · exact RegUpd.mem_write ..
  · exact RegUpd.rd_write ..
  · exact RegUpd.wr_write ..

theorem parameters_frame {s t : State} (p : Params)
    (keeps : Divide.Keeps Parameters.changed s t) :
    InitialBody.SameFrame (VG.Proof.Argon2.AArch64.Derive.dimensionState s p) t := by
  have frame := VG.Proof.Argon2.AArch64.Derive.dimension_frame s p
  refine ⟨?_, ?_, ?_, keeps.mem.trans frame.mem.symm,
    keeps.rd.trans frame.rd.symm, keeps.wr.trans frame.wr.symm⟩
  · exact (keeps.regs .x19 (by decide)).trans frame.bp.symm
  · exact (keeps.regs .x24 (by decide)).trans frame.bx.symm
  · exact keeps.sp.trans frame.sp.symm

theorem parameters_ready {s t : State} {p : Params}
    (h : InitialBody.Ready p (VG.Proof.Argon2.AArch64.Derive.dimensionState s p))
    (length : t.gpr .x21 = BitVec.ofNat 64 p.laneLen)
    (keeps : Divide.Keeps Parameters.changed s t) : InitialBody.Ready p t :=
  h.of_state (VG.Proof.Argon2.AArch64.Derive.parameters_frame p keeps) length

theorem parameters_body_ok (v : HPrime.Backend) (name : String)
    (s : State) (p : Params) (parameters : Parameters.Ready p s)
    (body : InitialBody.Ready p (VG.Proof.Argon2.AArch64.Derive.dimensionState s p)) :
    WP isa (.seq Impl.Argon2.AArch64.Parameters.code
      (Impl.Argon2.AArch64.InitialBody.code name v.hash)) s (InitialBody.Done s · p) := by
  refine WP.seq ((Parameters.code_ok s p parameters).mono ?_)
  rintro a ⟨length, keeps⟩
  refine (InitialBody.code_ok v name a p (VG.Proof.Argon2.AArch64.Derive.parameters_ready body length keeps)).mono ?_
  intro t done
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have base : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : FinalOutput.work a = FinalOutput.work s := by
    unfold FinalOutput.work; rw [keeps.mem, bp]
  have output : FinalOutput.output a = FinalOutput.output s := by
    unfold FinalOutput.output; rw [keeps.mem, bp]
  refine ⟨?_, done.bp.trans bp, done.sp.trans sp,
    done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, ?_⟩
  · have digest := done.digest
    simp only [Initial.inputBytes, Initial.wordAt, keeps.mem, bp, output] at digest
    exact digest
  · have frame := done.frame
    rw [InitFill.writes_eq s a p bp sp base work output] at frame
    rw [keeps.mem] at frame
    exact frame
  · intro r hr
    have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], r ∉ Parameters.changed := by decide
    exact (done.unused r hr).trans (keeps.regs r (facts r hr))

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveInputBytes`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveMemorySpace`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveHashSpace`. -/
section
/-! Permissions for H₀ follow from the signature and the private ABI frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_hash_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Initial.Space t := by
  have scratch := VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared
  have member : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  refine ⟨private_stack_minimum h prepared, ?_, ?_, ?_, private_frame_stack prepared 16 (by decide), ?_,
    by simpa only [BitVec.add_zero] using private_local_write prepared 0 64 (by decide)⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) member 16 (by decide)
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) member
  · intro d hd
    have bounds : ∀ d ∈ Initial.slots, d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveHashInputs`. -/
section
/-! All four secret inputs keep their original pointers and lengths in the private frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Proof.Argon2.AArch64.Initial (wordAt inputRegion)

theorem private_input_member {s t : State} (words : VG.Proof.Argon2.AArch64.Derive.DeriveWords s t) (input : Nat × Nat)
    (member : input ∈ Initial.inputs) : VG.Proof.Argon2.AArch64.Initial.inputRegion t input.1 input.2 ∈ abiInputs s := by
  simp only [Initial.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · change (⟨VG.Proof.Argon2.AArch64.Initial.wordAt t 104, (VG.Proof.Argon2.AArch64.Initial.wordAt t 96).toNat⟩ : Region) ∈ abiInputs s
    rw [words.password, words.passwordLength]
    exact List.mem_cons_self ..
  · change (⟨VG.Proof.Argon2.AArch64.Initial.wordAt t 88, (VG.Proof.Argon2.AArch64.Initial.wordAt t 80).toNat⟩ : Region) ∈ abiInputs s
    rw [words.salt, words.saltLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · change (⟨VG.Proof.Argon2.AArch64.Initial.wordAt t 200, (VG.Proof.Argon2.AArch64.Initial.wordAt t 208).toNat⟩ : Region) ∈ abiInputs s
    rw [words.secret, words.secretLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · change (⟨VG.Proof.Argon2.AArch64.Initial.wordAt t 216, (VG.Proof.Argon2.AArch64.Initial.wordAt t 224).toNat⟩ : Region) ∈ abiInputs s
    rw [words.ad, words.adLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem private_hash_inputs {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    ∀ input ∈ Initial.inputs, Initial.InputReady t input.1 input.2 := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have space := VG.Proof.Argon2.AArch64.Derive.private_hash_space h prepared
  have separation := VG.Proof.Argon2.AArch64.Derive.abi_separation h
  have scratch := VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared
  intro input hi
  have region := VG.Proof.Argon2.AArch64.Derive.private_input_member words input hi
  have facts : ∀ input ∈ Initial.inputs, input.1 ∈ Initial.slots ∧ input.2 ∈ Initial.slots ∧
      input.1 + 8 ≤ 272 ∧ input.2 + 8 ≤ 272 := by decide
  obtain ⟨pointerSlot, lengthSlot, pointerBound, lengthBound⟩ := facts input hi
  have buffer : (VG.Proof.Argon2.AArch64.Initial.inputRegion t input.1 input.2, false) ∈ abiBuffers s ++ [(abiArguments s, false)] :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, region, rfl⟩))
  refine ⟨space, pointerSlot, lengthSlot, pointerBound, lengthBound,
    VG.Proof.Argon2.AArch64.Derive.abi_input_lengths h _ region, ?_, ?_, ?_⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    rw [prepared.rd]
    change VG.Proof.Argon2.AArch64.Initial.inputRegion t input.1 input.2 ∈ (frameStart s Impl.Argon2.AArch64.Derive.saved).rd
    rw [frameStart_rd, h.rd]
    exact List.mem_append_left _ region
  · rw [scratch]; exact separation.inputWork _ region
  · exact (private_stack_disjoint h prepared (VG.Proof.Argon2.AArch64.Initial.inputRegion t input.1 input.2, false) buffer 16 (by decide)).symm

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveAllocations`. -/
section
/-! The exact matrix and output allocations of the signature remain writable. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_matrix_region {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
  rw [words.matrix, ← h.blocks]; rfl

theorem private_local_cover {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 272) : Covers [⟨t.gpr .x19, n⟩] t.wr := by
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨⟨t.gpr .x19, 272⟩, ?_, ?_⟩
  · rw [prepared.wr, prepared.bp]
    exact frameStart_locals s _
  · unfold Region.Contains at hc ⊢
    exact Nat.le_trans hc bound

theorem private_matrix_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩] t.wr := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have member : abiMatrix s ∈ t.wr := private_wr_member prepared _ (by rw [h.wr]; exact List.mem_cons_self ..)
  have matrix : (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
    change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
    rw [words.matrix, ← h.blocks]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiMatrix s, member, matrix ▸ hc⟩

theorem private_output_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FinalOutput.output t, (abiParams s).tagLen⟩] t.wr := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have member : abiOutput s ∈ t.wr := private_wr_member prepared _ (by
    rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiOutput s, member, output ▸ hc⟩

theorem private_work_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (n : Nat) (bound : n ≤ 16384) :
    Covers [⟨FinalOutput.work t, n⟩] t.wr := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨abiWork s, private_work_member h prepared, ?_⟩
  change Region.Contains ⟨abiWord s 56, 16384⟩ p k
  have pointer : FinalOutput.work t = abiWord s 56 := words.work
  rw [pointer] at hc
  unfold Region.Contains at hc ⊢
  exact Nat.le_trans hc bound

end VG.Proof.Argon2.AArch64.Derive
end

/-! The signature's rounded block allocation supplies all initialization permissions. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_matrix_bytes {s : State} (h : AbiEnvironment s) :
    1024 * ((abiParams s).lanes * (abiParams s).laneLen) = (abiParams s).blocks * 1024 := by
  rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1, Nat.mul_comm]

theorem private_memory_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    MemoryInit.Space t (FillKernel.matrix t)
      (1024 * ((abiParams s).lanes * (abiParams s).laneLen)) := by
  have matrix := VG.Proof.Argon2.AArch64.Derive.private_matrix_region h prepared
  have separation := VG.Proof.Argon2.AArch64.Derive.abi_separation h
  have scratch := VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  rw [VG.Proof.Argon2.AArch64.Derive.private_matrix_bytes h]
  refine ⟨private_stack_minimum h prepared, VG.Proof.Argon2.AArch64.Derive.private_matrix_cover h prepared, VG.Proof.Argon2.AArch64.Derive.private_local_cover prepared 72 (by decide), ?_,
    ?_, ?_, ?_, (private_frame_stack prepared 16 (by decide)).symm, ?_, ?_, ?_⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [matrix]; exact private_frame_disjoint h prepared (abiMatrix s, true) matrixMember
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) workMember
  · rw [matrix, scratch]; exact separation.matrixWork
  · rw [matrix]; exact private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 16 (by decide)
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 16 (by decide)
  · have blocks := Proof.Argon2.blocks_le_memory (abiParams s)
    have memoryBound := h.valid.2.2.2.2.2.1
    omega

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveHeader`. -/
section
/-! H₀ hashes the original requested memory cost and the exact reviewed parameters. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_header {s t : State} (words : VG.Proof.Argon2.AArch64.Derive.DeriveWords s t) :
    Initial.headerBytes t = Proof.Argon2.initialHeader (abiParams s) := by
  have headerWords : (List.range 6).map (Initial.headerValue t) =
      [BitVec.ofNat 32 (abiParams s).lanes, BitVec.ofNat 32 (abiParams s).tagLen,
        BitVec.ofNat 32 (abiParams s).memory, BitVec.ofNat 32 (abiParams s).passes,
        19#32, BitVec.ofNat 32 (abiParams s).variant.code] := by
    change [(Initial.wordAt t 184).setWidth 32, (Initial.wordAt t 264).setWidth 32,
      (Initial.wordAt t 176).setWidth 32, (Initial.wordAt t 72).setWidth 32, 19#32,
      (Initial.wordAt t 112).setWidth 32] = _
    rw [words.lanes, words.tagLength, words.memory, words.passes, words.kind]
    simp only [BitVec.setWidth_ofNat_of_le (show 32 ≤ 64 by decide)]
  unfold Initial.headerBytes
  rw [← List.flatMap_map, headerWords]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc,
    Proof.Argon2.initialHeader, Spec.Argon2.le32]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveFinalLayout`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveFillLayout`. -/
section
/-! One reviewed allocation supplies all filling and address-generation ranges. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_fill_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillKernel.Layout (abiParams s) t := by
  have space := VG.Proof.Argon2.AArch64.Derive.private_memory_space h prepared
  rw [VG.Proof.Argon2.AArch64.Derive.private_matrix_bytes h] at space
  refine ⟨?_, private_local_write prepared 16 8 (by decide), space.matrix,
    VG.Proof.Argon2.AArch64.Derive.private_work_cover h prepared 5120 (by decide), ?_, space.frameMatrix.symm, ?_, ?_,
    private_frame_stack prepared 8 (by decide), ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 16, 184, 232, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · have pointer : t.gpr .x24 = FillKernel.work t := by
      rw [VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.AArch64.Derive.private_words h prepared).work.symm
    rw [← pointer]
    exact space.matrixWork.sub_right (Region.sub_prefix (by decide))
  · exact (space.stackMatrix.sub_left (below_sub (by decide) (by decide))).symm
  · have pointer : t.gpr .x24 = FillKernel.work t := by
      rw [VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.AArch64.Derive.private_words h prepared).work.symm
    rw [← pointer]
    exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · have pointer : t.gpr .x24 = FillKernel.work t := by
      rw [VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.AArch64.Derive.private_words h prepared).work.symm
    rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))

theorem private_address_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : AddressCalls.Ready t := by
  have space := VG.Proof.Argon2.AArch64.Derive.private_memory_space h prepared
  have pointer : t.gpr .x24 = AddressCalls.work t := by
    rw [VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared]; exact (VG.Proof.Argon2.AArch64.Derive.private_words h prepared).work.symm
  refine ⟨private_local_read prepared 248 8 (by decide), VG.Proof.Argon2.AArch64.Derive.private_work_cover h prepared 8192 (by decide),
    ?_, private_frame_stack prepared 8 (by decide), ?_⟩
  · rw [← pointer]; exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))

theorem private_fill_environment {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillSetup.Environment (abiParams s) t := by
  have space := VG.Proof.Argon2.AArch64.Derive.private_memory_space h prepared
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have pointer : t.gpr .x24 = AddressCalls.work t := by
    rw [VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared]; exact words.work.symm
  rw [VG.Proof.Argon2.AArch64.Derive.private_matrix_bytes h] at space
  refine ⟨?_, h.valid.2.2.2.1, VG.Proof.Argon2.AArch64.Derive.private_fill_layout h prepared, VG.Proof.Argon2.AArch64.Derive.private_address_layout h prepared, ?_,
    private_local_write prepared 8 8 (by decide), private_local_write prepared 0 8 (by decide),
    ?_, words.blocks, words.passes, words.kind, words.lanes⟩
  · refine ⟨h.valid.1, Nat.lt_trans h.valid.2.1 (by decide), h.valid.2.2.2.2.1,
      h.valid.2.2.2.2.2.1, by decide, h.valid.1, by decide⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 8, 72, 112, 240], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · rw [← pointer]; exact space.matrixWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.AArch64.Derive
end

/-! Final lane reduction and H′ use the matrix and disjoint output/scratch allocations. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_final_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FinalOutput.Ready (abiParams s) t := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have separation := VG.Proof.Argon2.AArch64.Derive.abi_separation h
  have environment := VG.Proof.Argon2.AArch64.Derive.private_fill_environment h prepared
  have parameters := environment.parameters
  have blocks := Proof.Argon2.lastIndex_bounds (abiParams s) parameters.lanesPositive
    parameters.segment_bound.1 0 parameters.lanesPositive
  have minimum : 1024 ≤ (abiParams s).blocks * 1024 := by
    have positive : 1 ≤ (abiParams s).blocks := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right 1024 positive
  have matrix := VG.Proof.Argon2.AArch64.Derive.private_matrix_region h prepared
  have work : FinalOutput.work t = (abiWork s).base := words.work
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have outputMember : (abiOutput s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have matrixWork : (⟨ReductionState.matrix t, 1024⟩ : Region).Disjoint ⟨FinalOutput.work t, 16384⟩ := by
    rw [work]
    apply Region.Disjoint.sub_left separation.matrixWork
    rw [← matrix]
    exact Region.sub_prefix minimum
  have stackMatrix : (below (t.sp) 16).Disjoint ⟨ReductionState.matrix t, 1024⟩ := by
    apply Region.Disjoint.sub_right
      (private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 16 (by decide))
    rw [← matrix]; exact Region.sub_prefix minimum
  refine ⟨private_stack_minimum h prepared, by have tag := h.valid.2.2.2.2.2.2.1; omega, h.valid.2.2.2.2.2.2.2.1,
    ?_, words.tagLength, ?_, VG.Proof.Argon2.AArch64.Derive.private_output_cover h prepared, ?_, matrixWork, ?_, stackMatrix, ?_, ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [232, 256, 264, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · intro p n ⟨region, member, contains⟩
    simp only [List.mem_singleton] at member; subst region
    have contained : Region.Contains ⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ p n := by
      unfold Region.Contains at contains ⊢; exact Nat.le_trans contains minimum
    obtain ⟨r, hr, hc⟩ := VG.Proof.Argon2.AArch64.Derive.private_matrix_cover h prepared p n ⟨_, List.mem_singleton_self _, contained⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [work]; exact private_work_member h prepared
  · rw [output, work]; exact separation.outputWork
  · rw [output]; exact private_stack_disjoint h prepared (abiOutput s, true) outputMember 16 (by decide)
  · rw [work]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 16 (by decide)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveBodyReady`. -/
section
/-! The shared API contract supplies the complete body's precondition after preparation. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem DeriveWords.of_state {s a b : State} (h : VG.Proof.Argon2.AArch64.Derive.DeriveWords s a) (k : InitialBody.SameFrame a b) :
    VG.Proof.Argon2.AArch64.Derive.DeriveWords s b :=
  ⟨(k.word 72).trans h.passes, (k.word 80).trans h.saltLength, (k.word 88).trans h.salt,
    (k.word 96).trans h.passwordLength, (k.word 104).trans h.password, (k.word 112).trans h.kind,
    (k.word 176).trans h.memory, (k.word 184).trans h.lanes, (k.word 200).trans h.secret,
    (k.word 208).trans h.secretLength, (k.word 216).trans h.ad, (k.word 224).trans h.adLength,
    (k.word 232).trans h.matrix, (k.word 240).trans h.blocks, (k.word 248).trans h.work,
    (k.word 256).trans h.output, (k.word 264).trans h.tagLength⟩

theorem private_body_ready {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    InitialBody.Ready (abiParams s) (VG.Proof.Argon2.AArch64.Derive.dimensionState t (abiParams s)) := by
  let a := VG.Proof.Argon2.AArch64.Derive.dimensionState t (abiParams s)
  have keeps : InitialBody.SameFrame t a := VG.Proof.Argon2.AArch64.Derive.dimension_frame t (abiParams s)
  have words : VG.Proof.Argon2.AArch64.Derive.DeriveWords s a := (VG.Proof.Argon2.AArch64.Derive.private_words h prepared).of_state keeps
  have matrix : FillKernel.matrix a = FillKernel.matrix t := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.bp]
  have scratch : a.gpr .x24 = FinalOutput.work a := by
    rw [keeps.bx, VG.Proof.Argon2.AArch64.Derive.private_scratch h prepared]
    exact words.work.symm
  refine ⟨keeps.hashSpace (VG.Proof.Argon2.AArch64.Derive.private_hash_space h prepared),
    fun input hi => keeps.input (VG.Proof.Argon2.AArch64.Derive.private_hash_inputs h prepared input hi), VG.Proof.Argon2.AArch64.Derive.private_header words, ?_⟩
  refine ⟨?_, (VG.Proof.Argon2.AArch64.Derive.private_fill_environment h prepared).of_state keeps.bp keeps.sp keeps.mem keeps.rd keeps.wr,
    keeps.output (VG.Proof.Argon2.AArch64.Derive.private_final_layout h prepared), h.valid.2.2.1, scratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, words.lanes, ?_, ?_⟩
  · rw [matrix]
    exact (VG.Proof.Argon2.AArch64.Derive.private_memory_space h prepared).same keeps.wr keeps.bp keeps.bx keeps.sp
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 232 8 (by decide)
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 184 8 (by decide)
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 240 8 (by decide)
  · rfl
  · rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1]; exact words.blocks
  · exact RegUpd.gpr_write_self ..

theorem private_pipeline_ok (v : HPrime.Backend) (name : String)
    (s t : State) (h : AbiEnvironment s) (prepared : PrivatePrepared (prologueState s) t) :
    WP isa (.seq Impl.Argon2.AArch64.Parameters.code
      (Impl.Argon2.AArch64.InitialBody.code name v.hash)) t (InitialBody.Done t · (abiParams s)) :=
  VG.Proof.Argon2.AArch64.Derive.parameters_body_ok v name t (abiParams s) (private_parameters h prepared) (VG.Proof.Argon2.AArch64.Derive.private_body_ready h prepared)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Saving registers and copying arguments leave all original input bytes unchanged. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_prepare_frame {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Frame [⟨(prologueState s).sp, 272⟩] (prologueState s).mem t.mem := by
  apply prepared.frame.sub
  intro region hr
  simp only [privateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

theorem private_prologue_frame {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Frame [below (s.sp) 384] s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.AArch64.Derive.saved (by
    have space := h.stack; change 384 ≤ (s.sp).toNat; omega)
  apply prologue.trans
  have preparation := VG.Proof.Argon2.AArch64.Derive.private_prepare_frame prepared
  rw [prologue_sp] at preparation
  exact preparation.sub (by
    intro region hr; simp only [List.mem_singleton] at hr; subst region
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)

theorem private_input_bytes {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (input : Nat × Nat) (hi : input ∈ Initial.inputs) :
    Initial.inputBytes t input.1 input.2 =
      Spec.Blake2.bytesAt s.mem (Initial.inputRegion t input.1 input.2).base
        (Initial.inputRegion t input.1 input.2).len := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have region := VG.Proof.Argon2.AArch64.Derive.private_input_member words input hi
  have buffer : (Initial.inputRegion t input.1 input.2, false) ∈ abiBuffers s ++ [(abiArguments s, false)] :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, region, rfl⟩))
  have disjoint := h.reserved (below (s.sp) 400)
    (List.mem_singleton_self _)
    (Initial.inputRegion t input.1 input.2, false) buffer
  have length := VG.Proof.Argon2.AArch64.Derive.abi_input_lengths h _ region
  apply Proof.Blake2.bytesAt_congr
  intro i hi'
  apply (VG.Proof.Argon2.AArch64.Derive.private_prologue_frame h prepared).bytes (R := Initial.inputRegion t input.1 input.2)
    _ (by omega) hi'
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact (disjoint.sub_left (below_sub (by decide) (by decide))).symm

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveReturn`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveRestore`. -/
section
/-! Reload all saved registers from their unchanged stack slots. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem frameEnd_sp (s : State) (rs : List Reg) :
    (frameEnd s rs).sp = s.sp + BitVec.ofNat 64 (272 + 16 * rs.length) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (frameEnd s rs).sp + 16 = _
    rw [ih, BitVec.add_assoc, show (16 : Addr) = BitVec.ofNat 64 16 from rfl,
      ← BitVec.ofNat_add]
    exact congrArg (fun n => s.sp + BitVec.ofNat 64 n)
      (by simp only [List.length_cons]; omega)

theorem popped_one_reg (s : State) (r : Reg) :
    (popped r s).gpr r = s.mem.readW s.sp 64 := by
  simp only [popped, RegUpd.gpr_write_self, BitVec.setWidth_eq]
  rfl

theorem frameEnd_restore (s : State) (rs : List Reg) (values : Reg → Addr)
    (distinct : rs.Nodup)
    (words : ∀ j (hj : j < rs.length),
      s.mem.readW (s.sp + BitVec.ofNat 64 (272 + 16 * rs.length - 16 * (j + 1))) 64 = values rs[j]) :
    ∀ r ∈ rs, (frameEnd s rs).gpr r = values r := by
  induction rs with
  | nil => intro r hr; exact False.elim (List.not_mem_nil hr)
  | cons r rs ih =>
    have nodup := List.nodup_cons.mp distinct
    have innerWords : ∀ j (hj : j < rs.length),
        s.mem.readW (s.sp + BitVec.ofNat 64 (272 + 16 * rs.length - 16 * (j + 1))) 64 = values rs[j] := by
      intro j hj
      have word := words (j + 1) (by simp only [List.length_cons]; omega)
      have offset : 272 + 16 * (r :: rs).length - 16 * (j + 1 + 1) =
          272 + 16 * rs.length - 16 * (j + 1) := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    have inner := ih nodup.2 innerWords
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [frameEnd, VG.Proof.Argon2.AArch64.Derive.popped_one_reg, frameEnd_mem, VG.Proof.Argon2.AArch64.Derive.frameEnd_sp]
      have word := words 0 (by simp)
      have offset : 272 + 16 * (x :: rs).length - 16 * (0 + 1) = 272 + 16 * rs.length := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    · change (popped r (frameEnd s rs)).gpr x = _
      have ne : x ≠ r := fun eq => nodup.1 (eq ▸ hx)
      change ((frameEnd s rs).write .x r
        ((frameEnd s rs).mem.readW (frameEnd s rs).sp 64)).gpr x = _
      rw [RegUpd.gpr_write_of_ne _ .x _ ne]
      exact inner x hx

theorem frame_restored (s t : State) (rs : List Reg)
    (distinct : rs.Nodup) (space : 272 + 16 * rs.length ≤ (s.sp).toNat)
    (sp : t.sp = (frameStart s rs).sp)
    (unchanged : ∀ j (_hj : j < rs.length),
      t.mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 =
        (frameStart s rs).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64) :
    ∀ r ∈ rs, (frameEnd t rs).gpr r = s.gpr r := by
  apply VG.Proof.Argon2.AArch64.Derive.frameEnd_restore t rs s.gpr distinct
  intro j hj
  have offsetBound : 16 * (j + 1) ≤ 272 + 16 * rs.length := by omega
  rw [sp, frameStart_sp, ← Offset.ofNat_sub_ofNat offsetBound, Offset.sub_add_sub_cancel,
    unchanged j hj]
  exact frameStart_word s rs space j hj

theorem frameEnd_reg (s : State) (rs : List Reg) (r : Reg) (other : r ∉ rs) :
    (frameEnd s rs).gpr r = s.gpr r := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at other
    change ((frameEnd s xs).write .x x
      ((frameEnd s xs).mem.readW (frameEnd s xs).sp 64)).gpr r = _
    rw [RegUpd.gpr_write_of_ne _ .x _ other.1, ih other.2]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveBodySaved`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveBodyPost`. -/
section
/-! The complete body's digest is the public API postcondition on original input memory. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_done_post {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    (Spec.Argon2.deriveContract AArch64.abi 400).post s u := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have password := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (104, 96) (by decide)
  have salt := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (88, 80) (by decide)
  have secret := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (200, 208) (by decide)
  have ad := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (216, 224) (by decide)
  change Initial.inputBytes t 104 96 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 104) (Initial.wordAt t 96).toNat at password
  change Initial.inputBytes t 88 80 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 88) (Initial.wordAt t 80).toNat at salt
  change Initial.inputBytes t 200 208 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 200) (Initial.wordAt t 208).toNat at secret
  change Initial.inputBytes t 216 224 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 216) (Initial.wordAt t 224).toNat at ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  have digest := done.digest
  change Spec.Blake2.bytesAt u.mem (Initial.wordAt t 256) (abiParams s).tagLen =
    Spec.Argon2.derive (abiParams s) (Initial.inputBytes t 104 96)
      (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) at digest
  rw [words.output, password, salt, secret, ad] at digest
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop]
  exact digest

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveBodyCorrect`. -/
section
/-! Preparation and the entire algorithm establish the shared API postcondition. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def bodyWrites (s : State) : List Region :=
  [abiMatrix s, abiWork s, abiOutput s, ⟨(prologueState s).sp, 272⟩,
    below ((prologueState s).sp) 16]

structure BodyDone (s t : State) : Prop where
  post : (Spec.Argon2.deriveContract AArch64.abi 400).post s t
  sp : t.sp = (prologueState s).sp
  rd : t.rd = (prologueState s).rd
  wr : t.wr = (prologueState s).wr
  frame : Frame (VG.Proof.Argon2.AArch64.Derive.bodyWrites s) (prologueState s).mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem private_body_frame {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    Frame (VG.Proof.Argon2.AArch64.Derive.bodyWrites s) (prologueState s).mem u.mem := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have matrix := VG.Proof.Argon2.AArch64.Derive.private_matrix_region h prepared
  have work : (⟨FinalOutput.work t, 16384⟩ : Region) = abiWork s := by
    change (⟨Initial.wordAt t 248, 16384⟩ : Region) = abiWork s
    rw [words.work]; rfl
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have body := done.frame
  rw [InitFill.writes, matrix, work, output, prepared.sp, prepared.bp] at body
  apply ((VG.Proof.Argon2.AArch64.Derive.private_prepare_frame prepared).mono ?_).trans (body.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    simp only [VG.Proof.Argon2.AArch64.Derive.bodyWrites, List.mem_cons, true_or, or_true]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [VG.Proof.Argon2.AArch64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [VG.Proof.Argon2.AArch64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [VG.Proof.Argon2.AArch64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨below ((prologueState s).sp) 16, by simp [VG.Proof.Argon2.AArch64.Derive.bodyWrites], fun _ h => h⟩
    · exact ⟨⟨(prologueState s).sp, 272⟩, by simp [VG.Proof.Argon2.AArch64.Derive.bodyWrites], Region.sub_prefix (by decide)⟩

theorem body_ok (v : HPrime.Backend) (name : String) (s : State) (h : AbiEnvironment s) :
    WP isa (Impl.Argon2.AArch64.Derive.body name v.hash) (prologueState s) (VG.Proof.Argon2.AArch64.Derive.BodyDone s) := by
  unfold Impl.Argon2.AArch64.Derive.body
  refine WP.seq ((prologue_prepare s h).mono ?_)
  intro t prepared
  refine (VG.Proof.Argon2.AArch64.Derive.private_pipeline_ok v name s t h prepared).mono ?_
  intro u done
  refine ⟨VG.Proof.Argon2.AArch64.Derive.private_done_post h prepared done, done.sp.trans prepared.sp,
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, VG.Proof.Argon2.AArch64.Derive.private_body_frame h prepared done, ?_⟩
  intro r hr
  have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
      r ∈ FillCompress.loopRegs ∧ r ≠ .x19 ∧ r ≠ .x24 := by decide
  obtain ⟨member, h19, h24⟩ := facts r hr
  exact (done.unused r hr).trans
    ((prepared.regs r member h19 h24).trans (frameStart_reg s _ r))

end VG.Proof.Argon2.AArch64.Derive
end

/-! The whole body leaves the prologue's six saved-register slots untouched. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def savedSlot (s : State) (j : Nat) : Region :=
  ⟨s.sp - BitVec.ofNat 64 (16 * (j + 1)), 8⟩

theorem saved_slot_sub (s : State) (j : Nat) (bound : j < 7) :
    Region.Sub (VG.Proof.Argon2.AArch64.Derive.savedSlot s j) (below (s.sp) 400) :=
  Offset.sub_below _ (by omega) (by omega)

theorem saved_slot_address (s : State) (j : Nat) (bound : j < 7) :
    (VG.Proof.Argon2.AArch64.Derive.savedSlot s j).base = (prologueState s).sp + BitVec.ofNat 64 (384 - 16 * (j + 1)) := by
  rw [prologue_sp]
  exact Offset.sub_ofNat_eq _ (by omega)

theorem saved_slot_buffers {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 7)
    (buffer : Region × Bool) (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (VG.Proof.Argon2.AArch64.Derive.savedSlot s j).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (VG.Proof.Argon2.AArch64.Derive.saved_slot_sub s j bound)

theorem saved_slot_writes {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 7) :
    ∀ r ∈ VG.Proof.Argon2.AArch64.Derive.bodyWrites s, (VG.Proof.Argon2.AArch64.Derive.savedSlot s j).Disjoint r := by
  intro r hr
  simp only [VG.Proof.Argon2.AArch64.Derive.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · apply VG.Proof.Argon2.AArch64.Derive.saved_slot_buffers h j bound (abiMatrix s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply VG.Proof.Argon2.AArch64.Derive.saved_slot_buffers h j bound (abiWork s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply VG.Proof.Argon2.AArch64.Derive.saved_slot_buffers h j bound (abiOutput s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · change (⟨(VG.Proof.Argon2.AArch64.Derive.savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [VG.Proof.Argon2.AArch64.Derive.saved_slot_address s j bound]
    exact Offset.disjoint_base _ (by omega) (by omega)
  · change (⟨(VG.Proof.Argon2.AArch64.Derive.savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [VG.Proof.Argon2.AArch64.Derive.saved_slot_address s j bound]
    exact Offset.disjoint_below _ (by omega)

theorem BodyDone.saved {s t : State} (h : AbiEnvironment s) (done : VG.Proof.Argon2.AArch64.Derive.BodyDone s t) (j : Nat) (bound : j < 7) :
    t.mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 =
      (prologueState s).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 :=
  done.frame.readW (r := VG.Proof.Argon2.AArch64.Derive.savedSlot s j) (Region.contains_self _ _) (VG.Proof.Argon2.AArch64.Derive.saved_slot_writes h j bound) (by decide)

end VG.Proof.Argon2.AArch64.Derive
end

/-! The nested ABI frames return the complete result and restore all saved registers. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def wholeWrites (s : State) : List Region := [abiMatrix s, abiWork s, abiOutput s, below (s.sp) 400]

theorem BodyDone.whole_frame {s t : State} (h : AbiEnvironment s) (done : VG.Proof.Argon2.AArch64.Derive.BodyDone s t) :
    Frame (VG.Proof.Argon2.AArch64.Derive.wholeWrites s) s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.AArch64.Derive.saved (by
    have space := h.stack; change 384 ≤ (s.sp).toNat; omega)
  apply (prologue.sub ?_).trans (done.frame.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨below (s.sp) 400, by simp [VG.Proof.Argon2.AArch64.Derive.wholeWrites], below_sub (by decide) (by decide)⟩
  · intro r hr
    simp only [VG.Proof.Argon2.AArch64.Derive.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [VG.Proof.Argon2.AArch64.Derive.wholeWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [VG.Proof.Argon2.AArch64.Derive.wholeWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [VG.Proof.Argon2.AArch64.Derive.wholeWrites], fun _ h => h⟩
    · refine ⟨below (s.sp) 400, by simp [VG.Proof.Argon2.AArch64.Derive.wholeWrites], ?_⟩
      rw [prologue_sp]
      exact Offset.sub_below _ (by decide) (by decide)
    · refine ⟨below (s.sp) 400, by simp [VG.Proof.Argon2.AArch64.Derive.wholeWrites], ?_⟩
      rw [prologue_sp]
      unfold below
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Region.sub_prefix (by decide)

theorem return_post {s t : State} (done : VG.Proof.Argon2.AArch64.Derive.BodyDone s t) :
    (Spec.Argon2.deriveContract AArch64.abi 400).post s (frameEnd t Impl.Argon2.AArch64.Derive.saved) := by
  have post := done.post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop]
  exact post

theorem code_wp (v : HPrime.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    WP isa (Impl.Argon2.AArch64.Derive.code name v.hash) s fun t =>
      (Spec.Argon2.deriveContract AArch64.abi 400).post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ Frame (VG.Proof.Argon2.AArch64.Derive.wholeWrites s) s.mem t.mem := by
  have h := abi_environment s pre
  unfold Impl.Argon2.AArch64.Derive.code
  apply frame_ok s Impl.Argon2.AArch64.Derive.saved _ _
    (by have space := h.stack; change 384 ≤ (s.sp).toNat; omega)
  refine (VG.Proof.Argon2.AArch64.Derive.body_ok v name s h).mono ?_
  intro t done
  refine ⟨done.sp, done.wr, VG.Proof.Argon2.AArch64.Derive.return_post done, ?_, ?_, ?_⟩
  · have restored := VG.Proof.Argon2.AArch64.Derive.frame_restored s t Impl.Argon2.AArch64.Derive.saved (by decide)
      (by have space := h.stack; change 384 ≤ (s.sp).toNat; omega) done.sp
      (fun j hj => done.saved h j hj)
    intro r hr
    have member : ∀ r ∈ preserved,
        r ∈ Impl.Argon2.AArch64.Derive.saved ∨ r ∈ [Reg.x25, .x26, .x27, .x28] := by decide
    rcases member r hr with hr | hr
    · exact restored r hr
    · have other : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
          r ∉ Impl.Argon2.AArch64.Derive.saved := by decide
      exact (VG.Proof.Argon2.AArch64.Derive.frameEnd_reg t _ r (other r hr)).trans (done.unused r hr)
  · exact (frameEnd_metadata s t Impl.Argon2.AArch64.Derive.saved done.sp done.wr).1
  · rw [frameEnd_mem]
    exact done.whole_frame h

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DerivePublic`. -/
section
/-! The public entry-point relation reads u32 arguments at their declared width. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure AbiPublic (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ [.x1, .x2, .x3, .x4], s.gpr r = t.gpr r
  smallRegs : ∀ r ∈ [.x0, .x5, .x6, .x7], (s.gpr r).setWidth 32 = (t.gpr r).setWidth 32
  smallWords : ∀ d ∈ [0], (abiWord s d).setWidth 32 = (abiWord t d).setWidth 32
  words : ∀ d ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72], abiWord s d = abiWord t d
  references : Spec.Argon2.references (abiParams s)
      (Spec.Blake2.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Blake2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 8) (abiWord s 16).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 24) (abiWord s 32).toNat) =
    Spec.Argon2.references (abiParams t)
      (Spec.Blake2.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat)
      (Spec.Blake2.bytesAt t.mem (t.gpr .x3) (t.gpr .x4).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 8) (abiWord t 16).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 24) (abiWord t 32).toNat)

theorem abi_public (s t : State) (h : (Spec.Argon2.deriveContract AArch64.abi 400).pub s t) :
    VG.Proof.Argon2.AArch64.Derive.AbiPublic s t := by
  sig_pub [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at h
  all_goals simp only [BitVec.add_zero] at *
  sig_split h
  constructor
  all_goals sig_eval [abiWord, abiParams]
  all_goals try simp only [BitVec.add_zero]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

theorem AbiPublic.params {s t : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiPublic s t) : abiParams s = abiParams t := by
  unfold abiParams
  rw [h.smallRegs .x0 (by simp), h.smallRegs .x5 (by simp),
    h.smallRegs .x6 (by simp), h.smallRegs .x7 (by simp), h.words 72 (by simp)]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DerivePrivatePublic`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveParametersCT`. -/
section
/-! Parameter calculation followed by the complete body obeys the reviewed leakage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64 VG.Spec.Argon2

structure ParametersRelated (p : Params) (s t : State) : Prop where
  left : Parameters.Ready p s
  right : Parameters.Ready p t
  body : InitialBody.ReviewedRelated p (VG.Proof.Argon2.AArch64.Derive.dimensionState s p) (VG.Proof.Argon2.AArch64.Derive.dimensionState t p)

theorem parameters_body_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (VG.Proof.Argon2.AArch64.Derive.ParametersRelated p)
      (.seq Impl.Argon2.AArch64.Parameters.code
        (Impl.Argon2.AArch64.InitialBody.code name v.hash)) (fun _ _ => True) := by
  have preparation := (Parameters.code_rel.mono (P' := VG.Proof.Argon2.AArch64.Derive.ParametersRelated p)
    (fun s t h => by
      have left := VG.Proof.Argon2.AArch64.Derive.dimension_frame s p
      have right := VG.Proof.Argon2.AArch64.Derive.dimension_frame t p
      exact ⟨left.bp.symm.trans (h.body.hashing.bp.trans right.bp),
        left.sp.symm.trans (h.body.hashing.sp.trans right.sp)⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Parameters.code_ok s p h.left, Parameters.code_ok t p h.right⟩)
  refine preparation.seq ((InitialBody.reviewed_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, h, ⟨length₁, keeps₁⟩, ⟨length₂, keeps₂⟩⟩
  exact h.body.of_state (VG.Proof.Argon2.AArch64.Derive.parameters_frame p keeps₁) (VG.Proof.Argon2.AArch64.Derive.parameters_frame p keeps₂) length₁ length₂

end VG.Proof.Argon2.AArch64.Derive
end

/-! Private argument copies retain exactly the reviewed public relation. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Proof.Argon2.AArch64.Initial (wordAt)

theorem DeriveWords.public_words {s₁ s₂ t₁ t₂ : State} (h : VG.Proof.Argon2.AArch64.Derive.AbiPublic s₁ s₂)
    (left : VG.Proof.Argon2.AArch64.Derive.DeriveWords s₁ t₁) (right : VG.Proof.Argon2.AArch64.Derive.DeriveWords s₂ t₂) :
    ∀ d ∈ Initial.slots, VG.Proof.Argon2.AArch64.Initial.wordAt t₁ d = VG.Proof.Argon2.AArch64.Initial.wordAt t₂ d := by
  intro d hd
  simp only [Initial.slots, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [left.passes, right.passes, h.params]
  · rw [left.saltLength, right.saltLength]; exact h.regs .x4 (by simp)
  · rw [left.salt, right.salt]; exact h.regs .x3 (by simp)
  · rw [left.passwordLength, right.passwordLength]; exact h.regs .x2 (by simp)
  · rw [left.password, right.password]; exact h.regs .x1 (by simp)
  · rw [left.kind, right.kind, h.params]
  · rw [left.memory, right.memory, h.params]
  · rw [left.lanes, right.lanes, h.params]
  · rw [left.secret, right.secret]; exact h.words 8 (by simp)
  · rw [left.secretLength, right.secretLength]; exact h.words 16 (by simp)
  · rw [left.ad, right.ad]; exact h.words 24 (by simp)
  · rw [left.adLength, right.adLength]; exact h.words 32 (by simp)
  · rw [left.tagLength, right.tagLength, h.params]

def abiReferences (s : State) : List Nat := Spec.Argon2.references (abiParams s)
  (Spec.Blake2.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  (Spec.Blake2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 8) (abiWord s 16).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 24) (abiWord s 32).toNat)

theorem private_references {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    InitialBody.references (abiParams s) t = VG.Proof.Argon2.AArch64.Derive.abiReferences s := by
  have words := VG.Proof.Argon2.AArch64.Derive.private_words h prepared
  have password := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (104, 96) (by decide)
  have salt := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (88, 80) (by decide)
  have secret := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (200, 208) (by decide)
  have ad := VG.Proof.Argon2.AArch64.Derive.private_input_bytes h prepared (216, 224) (by decide)
  simp only [Initial.inputRegion] at password salt secret ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  unfold InitialBody.references VG.Proof.Argon2.AArch64.Derive.abiReferences
  change Spec.Argon2.references (abiParams s) (Initial.inputBytes t 104 96)
    (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) = _
  rw [password, salt, secret, ad]

theorem private_parameters_related {s₁ s₂ t₁ t₂ : State}
    (left : AbiEnvironment s₁) (right : AbiEnvironment s₂) (h : VG.Proof.Argon2.AArch64.Derive.AbiPublic s₁ s₂)
    (prepared₁ : PrivatePrepared (prologueState s₁) t₁)
    (prepared₂ : PrivatePrepared (prologueState s₂) t₂) :
    VG.Proof.Argon2.AArch64.Derive.ParametersRelated (abiParams s₁) t₁ t₂ := by
  have same := h.params
  have ready₁ := VG.Proof.Argon2.AArch64.Derive.private_body_ready left prepared₁
  have ready₂ := VG.Proof.Argon2.AArch64.Derive.private_body_ready right prepared₂
  rw [← same] at ready₂
  have keeps₁ := VG.Proof.Argon2.AArch64.Derive.dimension_frame t₁ (abiParams s₁)
  have keeps₂ := VG.Proof.Argon2.AArch64.Derive.dimension_frame t₂ (abiParams s₁)
  have words₁ := (VG.Proof.Argon2.AArch64.Derive.private_words left prepared₁).of_state keeps₁
  have words₂ := (VG.Proof.Argon2.AArch64.Derive.private_words right prepared₂).of_state keeps₂
  have sp : t₁.sp = t₂.sp := by rw [prepared₁.sp, prepared₂.sp, prologue_sp, prologue_sp, h.sp]
  have bp : t₁.gpr .x19 = t₂.gpr .x19 := by rw [prepared₁.bp, prepared₂.bp, prologue_sp, prologue_sp, h.sp]
  have bx : t₁.gpr .x24 = t₂.gpr .x24 := by
    rw [VG.Proof.Argon2.AArch64.Derive.private_scratch left prepared₁, VG.Proof.Argon2.AArch64.Derive.private_scratch right prepared₂]
    exact h.words 56 (by simp)
  refine ⟨private_parameters left prepared₁, same.symm ▸ private_parameters right prepared₂, ?_⟩
  refine ⟨ready₁, ready₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨ready₁.hashSpace, ready₁.inputs⟩,
      ⟨ready₂.hashSpace, ready₂.inputs⟩, ?_, ?_, ?_, ?_⟩
    · rw [keeps₁.bp, keeps₂.bp]; exact bp
    · rw [keeps₁.bx, keeps₂.bx]; exact bx
    · rw [keeps₁.sp, keeps₂.sp]; exact sp
    · exact words₁.public_words h words₂
  · exact words₁.matrix.trans ((h.words 40 (by simp)).trans words₂.matrix.symm)
  · exact words₁.output.trans ((h.words 64 (by simp)).trans words₂.output.symm)
  · exact words₁.work.trans ((h.words 56 (by simp)).trans words₂.work.symm)
  · unfold InitialBody.references
    simp only [keeps₁.inputBytes, keeps₂.inputBytes]
    change InitialBody.references (abiParams s₁) t₁ = InitialBody.references (abiParams s₁) t₂
    rw [VG.Proof.Argon2.AArch64.Derive.private_references left prepared₁, same, VG.Proof.Argon2.AArch64.Derive.private_references right prepared₂]
    exact h.references

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DerivePreserved`. -/
section
/-! The complete derivation preserves SIMD registers for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

local notation "property" => keepsV

theorem initial_preservedV (v : HPrime.Backend) :
    (Impl.Argon2.AArch64.Initial.code v.hash).allInstrs property = true := by
  have init : v.hash.init.allInstrs property = true := v.initV
  have update : v.hash.update.allInstrs property = true := v.updateV
  have finalize : v.hash.finalize.allInstrs property = true := v.finalizeV
  simp only [Impl.Argon2.AArch64.Initial.code, Impl.Argon2.AArch64.Initial.start,
    Impl.Argon2.AArch64.Initial.absorb, Impl.Argon2.AArch64.Initial.finish,
    Impl.Argon2.AArch64.HPrime.init, Impl.Argon2.AArch64.HPrime.absorbFixed,
    Impl.Argon2.AArch64.HPrime.update, Impl.Argon2.AArch64.HPrime.finalize, Code.allInstrs]
  rw [init, update, finalize]
  lit_decide

theorem memory_preservedV (v : HPrime.Backend) (name : String) :
    (Impl.Argon2.AArch64.MemoryInit.code name v.hash).allInstrs property = true := by
  simp only [Impl.Argon2.AArch64.MemoryInit.code, Impl.Argon2.AArch64.MemoryInit.clear,
    Impl.Argon2.AArch64.MemoryInit.lane, Impl.Argon2.AArch64.MemoryInit.block, Code.allInstrs]
  rw [HPrime.code_keepsV v]
  lit_decide

theorem frame_preservedV (body : Prog isa) (rs : List Reg) (h : body.allInstrs property = true) :
    (Impl.Argon2.AArch64.Derive.frame body rs).allInstrs property = true := by
  induction rs with
  | nil => simpa [Impl.Argon2.AArch64.Derive.frame, Code.allInstrs, keepsV, vdstOf] using h
  | cons r rs ih => simpa [Impl.Argon2.AArch64.Derive.frame, Code.allInstrs, keepsV, vdstOf] using ih

theorem code_preservedV (v : HPrime.Backend) (name : String) :
    (Impl.Argon2.AArch64.Derive.code name v.hash).allInstrs property = true := by
  unfold Impl.Argon2.AArch64.Derive.code
  apply VG.Proof.Argon2.AArch64.Derive.frame_preservedV
  simp only [Impl.Argon2.AArch64.Derive.body, Impl.Argon2.AArch64.InitialBody.code,
    Impl.Argon2.AArch64.InitFill.code, Impl.Argon2.AArch64.FillFinish.code,
    Impl.Argon2.AArch64.Finish.code, Impl.Argon2.AArch64.FinalOutput.code, Code.allInstrs]
  rw [VG.Proof.Argon2.AArch64.Derive.initial_preservedV v, VG.Proof.Argon2.AArch64.Derive.memory_preservedV v name, HPrime.code_keepsV v]
  lit_decide

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DerivePrepareCT`. -/
section
/-! Preparation addresses only fixed offsets of the public stack pointer. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem prepare_rel : RelCT isa (fun s t => s.sp = t.sp)
    Impl.Argon2.AArch64.Derive.prepare (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => False.elim (by
      have := RegSet.mem_ofList.mp hr
      exact List.not_mem_nil this)⟩) (by taint_decide)
end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveFrameCT`. -/
section
/-! Saving and restoring the private frame leaks only the public stack pointer. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem push_some {s t : State} {r : Reg} (h : isa.push (.push r) s = some t) : t = pushed r s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem alloc_some {s t : State} (h : isa.push (.alloc 272) s = some t) : t = allocated 272 s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem push_rel {r : Reg} {body : Prog isa} {P : State → State → Prop}
    (sp : ∀ s t, P s t → s.sp = t.sp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t)
      body (fun _ _ => True)) :
    RelCT isa P (.frame (.push r) body (.pop r)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      cases VG.Proof.Argon2.AArch64.Derive.push_some p₁
      cases VG.Proof.Argon2.AArch64.Derive.push_some p₂
      obtain ⟨eq, _⟩ := run _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      simp only [addrs, Exec.sp b₁, Exec.sp b₂, pushed, sp _ _ hp, eq]

theorem alloc_rel {body : Prog isa} {P : State → State → Prop}
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated 272 s ∧ b = allocated 272 t)
      body (fun _ _ => True)) :
    RelCT isa P (.frame (.alloc 272) body (.free 272)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      cases VG.Proof.Argon2.AArch64.Derive.alloc_some p₁
      cases VG.Proof.Argon2.AArch64.Derive.alloc_some p₂
      obtain ⟨eq, _⟩ := run _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨by simpa only [addrs, List.map_nil, List.nil_append, List.append_nil] using eq, trivial⟩

theorem frame_rel (rs : List Reg) (body : Prog isa) (P : State → State → Prop)
    (sp : ∀ s t, P s t → s.sp = t.sp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = frameStart s rs ∧ b = frameStart t rs)
      body (fun _ _ => True)) :
    RelCT isa P (Impl.Argon2.AArch64.Derive.frame body rs) (fun _ _ => True) := by
  induction rs generalizing P with
  | nil => exact VG.Proof.Argon2.AArch64.Derive.alloc_rel run
  | cons r rs ih =>
    apply VG.Proof.Argon2.AArch64.Derive.push_rel sp
    apply ih (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t) ?_ ?_
    · rintro a b ⟨s, t, hp, rfl, rfl⟩
      change s.sp - 16 = t.sp - 16
      rw [sp s t hp]
    · apply run.mono ?_ (fun _ _ h => h)
      rintro a b ⟨u, v, ⟨s, t, hp, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨s, t, hp, rfl, rfl⟩
end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveCorrect`. -/
section
/-! Functional correctness, termination, memory safety, and the ARM64 ABI. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem code_correct (v : HPrime.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    ∃ tr t, Exec isa (Impl.Argon2.AArch64.Derive.code name v.hash) s tr t ∧
      abiPreserved s t ∧ (Spec.Argon2.deriveContract AArch64.abi 400).post s t := by
  obtain ⟨tr, t, run, post, regs, sp, frame⟩ := VG.Proof.Argon2.AArch64.Derive.code_wp v name s pre
  exact ⟨tr, t, run, ⟨regs, sp, Exec.preservedV run (VG.Proof.Argon2.AArch64.Derive.code_preservedV v name)⟩, post⟩
end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveContract`. -/
section
/-! A concrete caller establishes satisfiability of the shared derivation contract. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

def satArgs : List Nat := [1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

def satMem (a : Addr) : Byte :=
  let d := a.toNat - 0x40000
  if 0x40000 ≤ a.toNat ∧ a.toNat < 0x40050 then
    ((BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.Derive.satArgs[d / 8]?.getD 0)) >>> (8 * (d % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .x5 => 1 | .x6 => 8 | .x7 => 1 | _ => 0
  sp := 0x40000
  c := false
  v _ := 0
  unknowns _ := 0
  mem := VG.Proof.Argon2.AArch64.Derive.satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 80⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem contract_sat : ∃ s, (Spec.Argon2.deriveContract AArch64.abi 400).pre s := by
  refine ⟨VG.Proof.Argon2.AArch64.Derive.satState, ?_⟩
  sig_sat_check [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr,
    List.range, List.range.loop, VG.Proof.Argon2.AArch64.Derive.satState, VG.Proof.Argon2.AArch64.Derive.satMem, VG.Proof.Argon2.AArch64.Derive.satArgs, Spec.Argon2.params, Spec.Argon2.valid,
    Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]
end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveCT`. -/
section
/-! The entire entry point leaks only the exact allowance of the shared contract. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def AbiRelated (s t : State) : Prop := AbiEnvironment s ∧ AbiEnvironment t ∧ VG.Proof.Argon2.AArch64.Derive.AbiPublic s t

def PrologueRelated (a b : State) : Prop := ∃ s t, VG.Proof.Argon2.AArch64.Derive.AbiRelated s t ∧ a = prologueState s ∧ b = prologueState t

theorem body_rel (v : HPrime.Backend) (name : String) :
    RelCT isa VG.Proof.Argon2.AArch64.Derive.PrologueRelated (Impl.Argon2.AArch64.Derive.body name v.hash) (fun _ _ => True) := by
  have preparation := (prepare_rel.mono (P' := VG.Proof.Argon2.AArch64.Derive.PrologueRelated) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      rw [prologue_sp, prologue_sp, h.2.2.sp]) (fun _ _ h => h)).wpDep (F := fun a b =>
        ∃ s, a = prologueState s ∧ AbiEnvironment s ∧ PrivatePrepared a b) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      exact ⟨(prologue_prepare s h.1).mono (fun _ prepared => ⟨s, rfl, h.1, prepared⟩),
        (prologue_prepare t h.2.1).mono (fun _ prepared => ⟨t, rfl, h.2.1, prepared⟩)⟩)
  unfold Impl.Argon2.AArch64.Derive.body
  apply preparation.seq
  apply (RelCT.exists_ (fun p => VG.Proof.Argon2.AArch64.Derive.parameters_body_rel v name p)).mono ?_ (fun _ _ h => h)
  rintro a b ⟨_, x, y, ⟨s, t, h, rfl, rfl⟩,
    ⟨u, hu, _, prepared₁⟩, ⟨w, hw, _, prepared₂⟩⟩
  have left : PrivatePrepared (prologueState s) a := prepared₁
  have right : PrivatePrepared (prologueState t) b := prepared₂
  exact ⟨abiParams s, VG.Proof.Argon2.AArch64.Derive.private_parameters_related h.1 h.2.1 h.2.2 left right⟩

theorem code_ct (v : HPrime.Backend) (name : String) :
    ConstantTime isa (Spec.Argon2.deriveContract AArch64.abi 400).pre
      (Spec.Argon2.deriveContract AArch64.abi 400).pub
      (Impl.Argon2.AArch64.Derive.code name v.hash) := by
  have full := VG.Proof.Argon2.AArch64.Derive.frame_rel Impl.Argon2.AArch64.Derive.saved _ VG.Proof.Argon2.AArch64.Derive.AbiRelated
    (fun _ _ h => h.2.2.sp) (VG.Proof.Argon2.AArch64.Derive.body_rel v name)
  exact (full.mono (fun s t h =>
    ⟨abi_environment s h.1, abi_environment t h.2.1, VG.Proof.Argon2.AArch64.Derive.abi_public s t h.2.2⟩)
    (fun _ _ h => h)).constantTime

end VG.Proof.Argon2.AArch64.Derive
end

/-! Complete ARM64 Argon2 verification against the reviewed shared API contract. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem verified (v : HPrime.Backend) (name : String) :
    Verified AArch64.target (Impl.Argon2.AArch64.Derive.code name v.hash)
      (Spec.Argon2.deriveContract AArch64.abi 400) :=
  ⟨VG.Proof.Argon2.AArch64.Derive.code_correct v name, VG.Proof.Argon2.AArch64.Derive.code_ct v name, VG.Proof.Argon2.AArch64.Derive.contract_sat⟩

theorem code_spSafe (v : HPrime.Backend) (name : String) :
    (Impl.Argon2.AArch64.Derive.code name v.hash).all (fun i => !isa.writesSp i) = true := by
  induction Impl.Argon2.AArch64.Derive.code name v.hash <;> simp_all [Code.all]
end VG.Proof.Argon2.AArch64.Derive

end
