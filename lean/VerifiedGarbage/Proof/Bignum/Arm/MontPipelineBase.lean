module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
import VerifiedGarbage.Proof.Bignum.Arm.Round

/-! The baseline scan specializes the same arithmetic interface as optimized scans. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm

theorem baseline_law : RoundLaw montRound := by
  intro s base size tmp a b mod acc n i inv ctx _ hdr hi ptr hT hB hInv
  exact montRound_ok s ctx hdr hi ptr hT hB hInv

theorem baseline_ct : RoundCTLaw montRound := by
  intro base size tmp a b mod acc n i _ hi
  exact montRound_ct hi

end VG.Proof.Bignum.Arm.MontPipeline
