module

public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) key generation on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.Arm

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers and `lr` in `scratch`; the functions it \
    calls use the 36 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.KeyGen.keyGen44
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.KeyGen.keyGen65
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.KeyGen.keyGen87
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.Arm
