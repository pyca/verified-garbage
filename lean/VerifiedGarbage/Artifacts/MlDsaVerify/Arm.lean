module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) verification on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.Arm

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers and `lr` in `scratch`; the functions it \
    calls use the 36 bytes of stack below the stack pointer.",
   "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results and the \
    comparison of the commitment hash are combined without a branch, so the only branches depend \
    on the signature (whether its hint is well formed and its `z` small enough)."]

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Verify.verify44
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Verify.verify65
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Verify.verify87
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify87_verified }]

end VG.Artifacts.MlDsaVerify.Arm
