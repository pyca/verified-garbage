module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaResponse.AArch64

/-- Emission metadata for the existing verified low-part norm helper. -/
def subLowNormApi : Api where
  module := "mldsa"
  name := "vg_mldsa_signed_sub_low_norm"
  sig := Spec.MlDsa.subLowNormSig
  writeArgs := true
  contracts := some fun A stack => Spec.MlDsa.subLowNormContract A stack
  summary := "Subtracts a signed inverse-transform result from a canonical polynomial, writes its high and signed low parts, and returns the strict low-part norm-check result."
  safety := ["The first input must be canonical modulo 8380417; the second must have signed coefficients strictly between -8380417 and 16760834.",
    "gamma2 must be 95232 or 261888; the norm bound must be between 1 and 524288 inclusive."]

def artifacts : List Artifact := [
  Spec.MlDsa.addNormApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.addNorm
    verified := Proof.MlDsa.AArch64.Optimized.Response.addNorm_verified },
  subLowNormApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    verified := Proof.MlDsa.AArch64.Optimized.Response.subLowNorm_verified }]

end VG.Artifacts.MlDsaResponse.AArch64
