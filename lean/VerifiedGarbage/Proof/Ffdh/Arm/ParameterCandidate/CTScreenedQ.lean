module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedAfterQ
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

/-! Reconstruct q after the early p witness using public widths and the existing divider. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def ScreenedQStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧ p.params.length ≤ p.params.bytes.length ∧
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = p.params.candidate ∧
  ((p.params.candidate - 1) / 2) % 2 = 1

theorem screenedQ_ct (v : RoundImpl) : RelCT isa (Two ScreenedQStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ v.name v.code) (fun _ _ => True) := by
  have halfTrace : RelCT isa (Two ScreenedQStart) VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ (fun _ _ => True) :=
    two_map (fun p => (p.params.out, p.params.length)) (fun _ _ h => h.1.read_context) halveQ_ct
  have half : RelCT isa (Two ScreenedQStart) VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ (Two ScreenedAfterQStart) :=
    two_post halfTrace (fun _ _ h => WP.mono (candidateHalveValue_ok h.1 h.2.2.1)
      (fun _ ⟨ctx, number, _, _, _⟩ => ⟨⟨ctx, number, h.2.2.2⟩, h.2.1⟩))
  exact half.seq (screenedAfterQ_ct v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
