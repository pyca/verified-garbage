module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Spec.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! Persistent memory facts for writing one canonical public comb context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

namespace CombBuilder

def slots : List Nat := [0,4,24,28,32,56,60]
def bits (p : Inputs) : Nat := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)
def bytes (p : Inputs) : Nat := 8 * Spec.Ffdh.generationPrecomputedWords p.k

structure Memory (p : Inputs) (sp : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  calls : KeyCallMemory p s
  fixed : s.sp = sp
  output : OutputBuffer p.output (bytes p) s
  workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,bytes p⟩
  domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,bytes p⟩
  localSeparate : Region.Disjoint ⟨State.addr sp,72⟩ ⟨State.addr p.output,bytes p⟩
  callSeparate : Region.Disjoint ⟨State.addr p.output,bytes p⟩ (FrameStack.belowA sp 48)
  bitsSaved : s.mem.readW (off (State.addr sp) 16) 32 = BitVec.ofNat 32 (bits p)
  rowsSaved : s.mem.readW (off (State.addr sp) 44) 32 = BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows (bits p))

theorem Memory.after_external {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (frame : Frame [⟨State.addr p.output,bytes p⟩] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = p.base) :
    Memory p sp t ∧ WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem := by
  have localSep : ∀ r ∈ [⟨State.addr p.output,bytes p⟩],
      (⟨State.addr s.sp,72⟩ : Region).Disjoint r := by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    rw [h.fixed]
    exact h.localSeparate
  have firstSub : (⟨State.addr s.sp,4⟩ : Region).Sub ⟨State.addr s.sp,72⟩ := by
    simpa only [off,BitVec.add_zero] using
      (Offset.sub_base (State.addr s.sp) (d := 0) (n := 4) (k := 72) (by decide))
  have ⟨ready, workspace⟩ := h.ready.after_external frame
    (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact h.workspaceSeparate)
    (by intro r hr; exact (localSep r hr).sub_left firstSub) rest ptr
  have localEq := WorkspaceEq.of_frame (by decide : 72 < 2^64) frame localSep
  have context := h.context.after_frame frame rest ptr
    (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact h.domainSeparate)
    (by
      intro d hd r hr
      have fit : d+4 ≤ 72 := by simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hd; omega
      exact (localSep r hr).sub_left (Offset.sub_base (State.addr s.sp) (d := d) (n := 4) (k := 72) fit))
  refine ⟨⟨context,ready,h.calls.after rest,rest.sp.trans h.fixed,h.output.after rest,
    h.workspaceSeparate,h.domainSeparate,h.localSeparate,h.callSeparate,?_,?_⟩,workspace⟩
  · have word := localEq.word (d := 16) (bits := 32) (by decide)
    rw [h.fixed] at word
    exact word.trans h.bitsSaved
  · have word := localEq.word (d := 44) (bits := 32) (by decide)
    rw [h.fixed] at word
    exact word.trans h.rowsSaved

theorem Memory.after_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (ready : ArithmeticReady p.base p.len p.w t)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem)
    (rest : Rest roundClobbers s t) : Memory p sp t := by
  have localSep : ∀ r ∈ [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48],
      (⟨State.addr s.sp,72⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.context.locals.separate
    · rw [FrameStack.belowA,FrameStack.addr_sub' h.calls.stack.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
  have localEq := WorkspaceEq.of_frame (by decide : 72 < 2^64) frame localSep
  have context := h.context.after_call h.calls frame rest ready.ptr (by
    intro d hd
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hd
    omega)
  refine ⟨context,ready,h.calls.after rest,rest.sp.trans h.fixed,h.output.after rest,
    h.workspaceSeparate,h.domainSeparate,h.localSeparate,h.callSeparate,?_,?_⟩
  · have word := localEq.word (d := 16) (bits := 32) (by decide)
    rw [h.fixed] at word
    exact word.trans h.bitsSaved
  · have word := localEq.word (d := 44) (bits := 32) (by decide)
    rw [h.fixed] at word
    exact word.trans h.rowsSaved

end CombBuilder
end VG.Proof.Ffdh.Arm
