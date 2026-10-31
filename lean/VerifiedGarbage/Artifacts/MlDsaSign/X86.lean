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

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign44_verified },
  Spec.MlDsa.sign65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign65_verified },
  Spec.MlDsa.sign87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign87_verified }]

end VG.Artifacts.MlDsaSign.X86
