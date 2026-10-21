module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDecompose
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentTail

/-! The entire native compact Miller–Rabin exponent setup has a public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

theorem expSetup_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expSetup (fun _ _ => True) :=
  decomposeDone_ct.seq (sigmaReady_ct.seq
    (exponentCopy_ct.seq (exponentHalfLoop_key_ct.seq exponentPower_ct)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
