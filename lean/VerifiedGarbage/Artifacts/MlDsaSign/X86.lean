module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-!
# ML-DSA (FIPS 204) signing on x86

Each function saves its caller's registers in a frame of 16 bytes below the
return address, and calls the primitives with their arguments pushed below
it: at most 5 arguments and the return address (24 bytes), and the 56 bytes
the samplers use (`stack := 96`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.X86

open VG.Proof.MlDsa.X86.Sign (prims)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function keeps its working space, `Â`, `ŝ₁`, `ŝ₂`, `t̂₀` and the polynomials of each iteration \
    in `scratch`, and calls the ML-DSA primitives (`vg_mldsa_*`) and the Keccak functions.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign44_verified },
  Spec.MlDsa.sign65Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign65_verified },
  Spec.MlDsa.sign87Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign87_verified }]

end VG.Artifacts.MlDsaSign.X86
