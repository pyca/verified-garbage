module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! The merged scalar multiply-add API, implemented with baseline integer instructions. -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarMulAddApi with
    target := X86_64.target
    doc := Spec.Ed25519.scalarMulAddApi.doc (notes := ["Computes the complete 512-bit \
      multiply-add before reducing it modulo the subgroup order a 64-bit word at a time. All three input scalars \
      may use all 256 bits. The function saves callee-saved registers and the output's address in `scratch`."])
    code := Impl.Ed25519.X86_64.scalarMulAdd
    contract := Spec.Ed25519.scalarMulAddContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarMulAdd_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519MulAdd.X86_64
