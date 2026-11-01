module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvImplies
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! # `vg_rsa_crt_values` on PPC64LE: verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE

/-- `vg_rsa_crt_values`. -/
theorem cv_verified [InvLaw] :
    Verified target VG.Impl.Rsa.PPC64LE.CrtValues.code (Spec.Rsa.crtValuesContract abi) :=
  Verified.of_correct cv_correct cv_ct cv_implies

end VG.Proof.Rsa.PPC64LE.CrtValues
