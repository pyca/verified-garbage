module

public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-DSA (FIPS 204) verification on x86 (32-bit)

The functions save their caller's registers in a frame of 16 bytes below
the return address; their calls of the primitives use the 80 bytes below
it: at most 5 arguments, the return address and the primitive's 56 bytes
(`stack := 96`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.X86

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in a frame of 16 bytes; its calls use \
    the 80 bytes of stack below it.",
   "It returns early only when the hint is malformed or `z` is out of bounds, which depend on the \
    signature alone. It samples every polynomial of `A` and `c` whatever the samplers return, \
    zeroing the output of a sampler that fails rather than branching on it, and compares `c~` \
    with the recomputed value without branching on the bytes."]

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Verify.verify44
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Verify.verify65
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Verify.verify87
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify87_verified }]

end VG.Artifacts.MlDsaVerify.X86
