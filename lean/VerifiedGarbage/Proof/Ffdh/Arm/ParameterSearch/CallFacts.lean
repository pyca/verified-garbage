module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Tape
import VerifiedGarbage.Proof.Framework.Omega

/-! The shared candidate contract's stack and incoming-argument separation facts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

structure CallFacts (p : SearchParams) (used : Nat) (sp : BitVec 32) : Prop where
  stackFits : 184 ≤ sp.toNat
  argsFits : sp.toNat + 20 ≤ 2 ^ 32
  outputArgs : (⟨State.addr p.c.out, p.c.length⟩ : Region).Disjoint ⟨State.addr sp, 20⟩
  usedArgs : (⟨State.addr (p.control + 112#32), 8⟩ : Region).Disjoint ⟨State.addr sp, 20⟩
  scratchArgs : (⟨State.addr p.c.base, 8 * p.c.capacity⟩ : Region).Disjoint ⟨State.addr sp, 20⟩
  stackOutput : (FrameStack.belowA sp 184).Disjoint ⟨State.addr p.c.out, p.c.length⟩
  stackUsed : (FrameStack.belowA sp 184).Disjoint ⟨State.addr (p.control + 112#32), 8⟩
  stackTape : (FrameStack.belowA sp 184).Disjoint
    ⟨State.addr (p.c.tape + BitVec.ofNat 32 used), p.c.bytes.length - used⟩
  stackScratch : (FrameStack.belowA sp 184).Disjoint ⟨State.addr p.c.base, 8 * p.c.capacity⟩
  stackArgs : (FrameStack.belowA sp 184).Disjoint ⟨State.addr sp, 20⟩

theorem SearchBuffers.callFacts {p : SearchParams} {s : State} (h : SearchBuffers p s) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) : CallFacts p used (s.sp - 24#32) := by
  have argsSub : (⟨State.addr (s.sp - 24#32), 20⟩ : Region).Sub (FrameStack.belowA s.sp 208) :=
    fun a ha => callArguments_sub h.below a (Region.sub_prefix (by decide : 20 ≤ 24) a ha)
  have stackSub := callStack_sub h.below
  have out := (h.stackSeparate ⟨State.addr p.c.out, p.c.length⟩ (by simp)).2
  have control := (h.stackSeparate ⟨State.addr p.control, 128⟩ (by simp)).2
  have scratch := (h.stackSeparate ⟨State.addr p.c.base, 8 * p.c.capacity⟩ (by simp)).2
  have tape := (h.stackSeparate ⟨State.addr p.c.tape, p.c.bytes.length⟩ (by simp)).2
  exact ⟨callStack_fits h.below, by have := callArguments_fits h.below; omega,
    (out.sub_left argsSub).symm, ((control.sub_left argsSub).sub_right p.used_sub).symm,
    (scratch.sub_left argsSub).symm, out.sub_left stackSub,
    (control.sub_left stackSub).sub_right p.used_sub,
    (tape.sub_left stackSub).sub_right (p.source_sub used room), scratch.sub_left stackSub,
    callStack_arguments_separate h.below⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
