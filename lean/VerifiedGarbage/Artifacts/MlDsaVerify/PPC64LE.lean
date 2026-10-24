module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) verification on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.PPC64LE

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r24`–`r31` and its return address in `scratch`; the functions \
    it calls use the 96 bytes of stack below the stack pointer.",
   "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results and the \
    comparison of the commitment hash are combined without a branch, so the only branches depend \
    on the signature (whether its hint is well formed and its `z` small enough)."]

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Verify.verify44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Verify.verify65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Verify.verify87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Verify.verify87_verified }]

end VG.Artifacts.MlDsaVerify.PPC64LE
