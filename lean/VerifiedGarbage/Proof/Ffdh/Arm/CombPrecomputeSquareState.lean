module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControl
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareCounter
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquare
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! Persistent basis state across the public square-loop counter writes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def squareWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr sp,72⟩,FrameStack.belowA sp 48]

theorem Memory.squareContextEq {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (frame : Frame (squareWrites p sp) s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
  apply WorkspaceEq.of_frame (by have := h.output.fits; omega) frame
  intro r hr
  simp only [squareWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.workspaceSeparate.symm
  · exact h.localSeparate.symm
  · exact h.callSeparate

def squareNarrowWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨off (State.addr sp) 68,4⟩,FrameStack.belowA sp 48]

def SquareCount (sp : BitVec 32) (n : Nat) (s : State) : Prop :=
  s.mem.readW (off (State.addr sp) 68) 32=BitVec.ofNat 32 n

theorem Memory.squareNarrowContextEq {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (frame : Frame (squareNarrowWrites p sp) s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
  apply WorkspaceEq.of_frame (by have := h.output.fits; omega) frame
  intro r hr
  simp only [squareNarrowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.workspaceSeparate.symm
  · exact h.localSeparate.symm.sub_right (Offset.sub_base _ (by decide))
  · exact h.callSeparate

theorem Memory.squareNarrowRead36 {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (frame : Frame (squareNarrowWrites p sp) s.mem t.mem) :
    t.mem.readW (off (State.addr sp) 36) 32=s.mem.readW (off (State.addr sp) 36) 32 := by
  apply frame.readW (r:=⟨off (State.addr sp) 36,4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [squareNarrowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  have sub : (⟨off (State.addr sp) 36,4⟩ : Region).Sub ⟨State.addr sp,72⟩ := Offset.sub_base _ (by decide)
  rcases hr with rfl|rfl|rfl
  · have sep := h.context.locals.separate
    rw [h.fixed] at sep
    exact sep.sub_left sub
  · exact Offset.disjoint _ (Or.inl (by decide : 36+4≤68)) (by decide) (by decide)
  · have fit : 48≤sp.toNat := by rw [←h.fixed]; exact h.calls.stack.fit
    rw [FrameStack.belowA,FrameStack.addr_sub' fit]
    exact ((Offset.below_disjoint _ (by decide : 48+72≤2^64)).symm).sub_left sub

theorem control68_state (s : State) {p : Inputs} {sp : BitVec 32} {E n : Nat}
    (h : Core p sp s) (power : Power5 p E s) {t : State}
    (mem : t.mem=s.mem.writeW (off (State.addr s.sp) 68) (BitVec.ofNat 32 n))
    (rest : Rest [.r3,.r12] s t) :
    Core p sp t ∧ Power5 p E t ∧ SquareCount sp n t ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have raw : Frame [⟨off (State.addr s.sp) 68,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,?_,r⟩
  · change t.mem.readW (off (State.addr sp) 68) 32=BitVec.ofNat 32 n
    rw [mem,←h.memory.fixed,Mem.readW_writeW_self32]
  · apply raw.sub
    intro region hr
    have eq := List.mem_singleton.mp hr
    subst region
    refine ⟨⟨off (State.addr sp) 68,4⟩,by simp [squareNarrowWrites],?_⟩
    rw [h.memory.fixed]
    exact fun _ hx => hx

theorem squaresInit_state (s : State) {p : Inputs} {sp : BitVec 32} {E : Nat}
    (h : Core p sp s) (power : Power5 p E s) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresInit) s fun t =>
      Core p sp t ∧ Power5 p E t ∧ SquareCount sp (Spec.Rsa.FixedBaseComb.rows (bits p)) t ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (squaresInit_raw s h.memory.context.locals (by rw [h.memory.fixed]; exact h.memory.rowsSaved)) ?_
  rintro t ⟨mem,rest⟩
  exact control68_state s h power mem rest

theorem squaresNext_state (s : State) {p : Inputs} {sp : BitVec 32} {E n : Nat}
    (h : Core p sp s) (power : Power5 p E s) (positive : 0<n) (fits : n<2^32)
    (counter : SquareCount sp n s) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext) s fun t =>
      Core p sp t ∧ Power5 p E t ∧ SquareCount sp (n-1) t ∧ t.z=decide (n-1=0) ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (squaresNext_raw s h.memory.context.locals positive fits (by rw [h.memory.fixed]; exact counter)) ?_
  rintro t ⟨⟨mem,zero⟩,rest⟩
  obtain ⟨core,pow,count,frame,r⟩ := control68_state s h power mem rest
  exact ⟨core,pow,count,zero,frame,r⟩

end VG.Proof.Ffdh.Arm.CombBuilder
