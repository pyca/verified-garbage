module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame

/-! Restrict saved arguments to exactly the slots a native subroutine reads. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

theorem SavedFrame.project {s : State} {values nextValues : Nat → BitVec 32} {slots nextSlots : List Nat}
    (h : SavedFrame values slots s) (subset : ∀ d ∈ nextSlots, d ∈ slots)
    (equal : ∀ d ∈ nextSlots, values d = nextValues d) : SavedFrame nextValues nextSlots s :=
  ⟨h.space, fun d hd => (h.saved d (subset d hd)).trans (equal d hd)⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
