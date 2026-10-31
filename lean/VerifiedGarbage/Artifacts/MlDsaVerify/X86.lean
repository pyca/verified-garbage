module

public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-!
# ML-DSA (FIPS 204) verification on x86 (32-bit)

The functions save their caller's registers in a frame of 16 bytes below
the return address; their calls of the primitives use the 80 bytes below
it: at most 5 arguments, the return address and the primitive's 56 bytes
(`stack := 96`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.X86

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Verify.verify44
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Verify.verify65
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Verify.verify87
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify87_verified }]

end VG.Artifacts.MlDsaVerify.X86
