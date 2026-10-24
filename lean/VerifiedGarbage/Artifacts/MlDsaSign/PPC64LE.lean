module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) signing on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.PPC64LE

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r24`–`r31` and its return address in `scratch`; the functions \
    it calls use the 96 bytes of stack below the stack pointer.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Sign.sign44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Sign.sign44_verified },
  Spec.MlDsa.sign65Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Sign.sign65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Sign.sign65_verified },
  Spec.MlDsa.sign87Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Sign.sign87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Sign.sign87_verified }]

end VG.Artifacts.MlDsaSign.PPC64LE
