module

public import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLane
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup
public import VerifiedGarbage.Proof.Argon2.AArch64.ReducePointers
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlock
public import VerifiedGarbage.Proof.Argon2.FinalReduction
public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount
public import VerifiedGarbage.Proof.Argon2.Contract

/-! Merged from `Proof.Argon2.AArch64.ReductionState`. -/

@[expose] public section

section

/-! Block zero is the accumulator; every lane's last block remains unchanged. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 232) 64

structure Ready (p : Params) (s : State) : Prop where
  positive : 0 < p.lanes
  minimum : 2 ≤ p.segmentLen
  bound : p.blocks * 1024 < 2 ^ 64
  read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8
  write : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  frame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  length : s.gpr .x20 = BitVec.ofNat 64 p.laneLen

structure Represents (p : Params) (memory : Array Block) (acc : Block) (s : State) : Prop where
  accumulator : blockAt s.mem (matrix s) = acc
  last : ∀ lane < p.lanes,
    blockAt s.mem (Proof.Argon2.matrixCell (matrix s) (Proof.Argon2.lastIndex p lane)) =
      memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock

theorem Ready.block_cover {p : Params} {s : State} (h : Ready p s) (k : Nat) (active : k < p.blocks) :
    Covers [⟨Proof.Argon2.matrixCell (matrix s) k, 1024⟩] s.wr := by
  have sub : Covers [⟨Proof.Argon2.matrixCell (matrix s) k, 1024⟩] [⟨matrix s, p.blocks * 1024⟩] :=
    Covers.of_sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨matrix s, p.blocks * 1024⟩, by simp, k * 1024, rfl, by change k * 1024 + 1024 ≤ p.blocks * 1024; omega⟩)
  exact fun a n ha => h.write a n (sub a n ha)

theorem Ready.accumulator_cover {p : Params} {s : State} (h : Ready p s) :
    Covers [⟨matrix s, 1024⟩] s.wr := by
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using h.block_cover 0 (by omega)

theorem Ready.of_keeps {p : Params} {s t : State} (h : Ready p s)
    (k : Divide.Keeps ReducePointers.changed s t) : Ready p t := by
  have bp := k.regs .x19 (by decide)
  have base : matrix t = matrix s := by unfold matrix; rw [k.mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (k.regs .x20 (by decide)).trans h.length⟩
  · rw [k.rd, k.wr, bp]; exact h.read
  · rw [base, k.wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_keeps {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : Represents p memory acc s) (k : Divide.Keeps ReducePointers.changed s t) : Represents p memory acc t := by
  have base : matrix t = matrix s := by unfold matrix; rw [k.mem, k.regs .x19 (by decide)]
  constructor
  · rw [k.mem, base]; exact h.accumulator
  · rw [k.mem, base]; exact h.last

end VG.Proof.Argon2.AArch64.ReductionState
end

/-! A lane reduction writes only the accumulator, retaining every last-lane block. -/

namespace VG.Proof.Argon2.AArch64.ReduceLane

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Done (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  ready : Ready p t
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (lane : Nat) (h : Ready p s) (active : lane < p.lanes)
    (laneWord : s.gpr .x24 = BitVec.ofNat 64 lane) (memory : Array Block) (acc : Block)
    (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.AArch64.ReduceLane.code s
      (Done s · p memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
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
  have base : matrix a = matrix s := by unfold matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have dest' : a.gpr .x0 = matrix a := dest.trans base.symm
  have src' : a.gpr .x1 = Proof.Argon2.matrixCell (matrix a) (Proof.Argon2.lastIndex p lane) := by rw [base]; exact src
  have sourceWrite : Covers [⟨a.gpr .x1, 1024⟩] a.wr := by rw [src']; exact ha.block_cover _ lastBounds.2
  have sourceRead : Covers [⟨a.gpr .x1, 1024⟩] (a.rd ++ a.wr) := by
    intro x n hx
    obtain ⟨r, hr, hc⟩ := sourceWrite x n hx
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have destWrite : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by rw [dest']; exact ha.accumulator_cover
  have sep : (⟨a.gpr .x1, 1024⟩ : Region).Disjoint ⟨a.gpr .x0, 1024⟩ := by
    rw [src', dest']
    simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
      Proof.Argon2.matrixCell_disjoint (matrix a) p.blocks (Proof.Argon2.lastIndex p lane) 0 ha.bound
        lastBounds.2 (by omega) (by omega)
  refine (ReduceBlock.code_ok a sourceRead destWrite sep).mono ?_
  rintro t ⟨written, frame, copied, mx⟩
  rw [dest'] at frame written
  have bp : t.gpr .x19 = a.gpr .x19 := copied.1 .x19 (by decide) (by decide) (by decide) (by decide)
  have base' : matrix t = matrix a := by
    unfold matrix
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
        Proof.Argon2.matrixCell_disjoint (matrix a) p.blocks (Proof.Argon2.lastIndex p j) 0 ha.bound
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
