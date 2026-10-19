module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks

/-! # ML-DSA (FIPS 204) signing on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.Arm

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves `r4`–`r11` and its return address in `scratch`; its calls use the 28 \
    bytes of stack below the stack pointer (the calls with a fifth argument push it there).",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa44
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign44_verified' },
  Spec.MlDsa.sign65Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa65
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign65_verified' },
  Spec.MlDsa.sign87Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa87
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign87_verified' }]

end VG.Artifacts.MlDsaSign.Arm
