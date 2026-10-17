module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivBody
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Call
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Entry state and saved-register separation for the callable private wrapper -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem freed_mem_eq (n : Nat) (s : State) : (freed n s).mem = s.mem := rfl

def entered (s : State) : State := allocated frameBytes (pcPushed s)

structure PrivFnInput (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  stackFit : stackBytes ≤ s.sp.toNat
  context : PrivContext g bs (entered s)
  output : s.gpr .r0 = g.output
  modulus : s.gpr .r2 = g.sources 0
  count : s.gpr .r3 = BitVec.ofNat 32 g.length

theorem PrivFnInput.savedAddr {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivFnInput g bs s) : State.addr (pcPushed s).sp = g.savedRegion.base := by
  have sp : (pcPushed s).sp = g.stack + BitVec.ofNat 32 frameBytes := by
    rw [← h.context.sp]
    exact (BitVec.sub_add_cancel _ _).symm
  rw [sp, h.context.valid.offsetAddr (by simp only [frameBytes]; decide)]
  rfl

theorem savedRegion_separate {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ bodyWrites g, g.savedRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.innerSaved.symm
  · unfold PrivGeometry.savedRegion PrivGeometry.calleeRegion FrameStack.belowA
    rw [h.stackBase, Offset.add_add]
    exact Offset.disjoint_base _ (by decide : 56 ≤ 56 + frameBytes)
      (by decide : 56 + frameBytes + 56 ≤ 2 ^ 64)
  · exact h.stackOutput.sub_left h.savedSub
  · exact h.stackWorkspace.sub_left h.savedSub

theorem PrivFnInput.saved {g : PrivGeometry} {bs : Fin 8 → List Byte} {s t : State}
    (h : PrivFnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem) :
    Spill.Saved t.mem (State.addr (pcPushed s).sp) s.gpr pcCalleeSaved := by
  have initial := pc_push_callee_saved s (by have := h.stackFit; simp only [stackBytes] at this; omega)
  apply initial.frame (lo := 0) (hi := 56) (by decide) frame
  intro r hr
  change (⟨State.addr (pcPushed s).sp + BitVec.ofNat 64 0, 56 - 0⟩ : Region).Disjoint r
  simp only [BitVec.add_zero, Nat.sub_zero, h.savedAddr]
  exact savedRegion_separate h.context.valid r hr
end VG.Proof.Rsa.Arm
