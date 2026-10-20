module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on AArch64: the producers of polynomials with 16-bit coefficients -/

@[expose] public section

namespace VG.Artifacts.MlKem16.AArch64

def artifacts : List Artifact := [
  Spec.MlKem.cbd2_16Api.artifact AArch64.target {
    code := Impl.MlKem.AArch64.Cbd16.code16
    verified := Proof.MlKem.AArch64.Cbd16W.verified }]

end VG.Artifacts.MlKem16.AArch64
