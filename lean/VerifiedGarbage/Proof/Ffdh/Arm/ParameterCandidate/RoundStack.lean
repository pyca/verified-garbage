module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The shared Miller–Rabin call writes below the caller's saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SavedFrame.after_round {s t : State} {base : BitVec 32} {capacity : Nat}
    {values : Nat → BitVec 32} {slots : List Nat} {rs : List Reg}
    (h : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (stackBelow : 56 ≤ s.sp.toNat)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have fit := bounds d hd
  rcases hr with rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ fit)
  · change (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
    rw [VG.Arm.addr_add (by have := h.space.nowrap; omega), FrameStack.addr_sub' stackBelow]
    exact Offset.disjoint_below _ (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
