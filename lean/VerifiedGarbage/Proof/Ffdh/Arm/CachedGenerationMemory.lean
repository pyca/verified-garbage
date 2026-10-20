module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Framework.Mem

/-! The immutable canonical context survives silent argument and flag operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem cachedGeneration_publicRel (s t : State) : cachedGenerationEnvironment.publicRel s t := trivial

theorem cachedGeneration_afterMem {p : Inputs} {s t : State}
    (h : cachedGenerationEnvironment.holds p s) (mem : t.mem = s.mem) (rest : Rest [] s t) :
    cachedGenerationEnvironment.holds p t := by
  have frame : Frame (keyCallWrites p s) s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact h.after frame (rest.mono (by simp [roundClobbers]))

end VG.Proof.Ffdh.Arm
