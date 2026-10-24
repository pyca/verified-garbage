module

public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-!
# ML-DSA (FIPS 204) key generation on x86 (32-bit)

The functions save their caller's registers in a frame of 16 bytes below
the return address; their calls of the primitives use the 80 bytes below
it: at most 5 arguments, the return address and the primitive's 56 bytes
(`stack := 96`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.X86

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in a frame of 16 bytes; its calls use \
    the 80 bytes of stack below it.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.KeyGen.keyGen44
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.KeyGen.keyGen65
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.KeyGen.keyGen87
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.X86
