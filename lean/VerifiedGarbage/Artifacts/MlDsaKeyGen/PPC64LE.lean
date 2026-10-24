module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) key generation on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.PPC64LE

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r24`–`r31` and its return address in `scratch`; the functions \
    it calls use the 96 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.PPC64LE
