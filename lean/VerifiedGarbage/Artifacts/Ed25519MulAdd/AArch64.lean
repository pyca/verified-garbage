module

public import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! The merged scalar multiply-add API, implemented with baseline integer instructions. -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact AArch64.target {
    notes := ["Computes the complete 512-bit \
      multiply-add before reducing it modulo the subgroup order a 64-bit word at a time. All three input scalars \
      may use all 256 bits. The function saves callee-saved registers in `scratch`."]
    code := Impl.Ed25519.AArch64.scalarMulAdd
    verified := Proof.Ed25519.AArch64.scalarMulAdd_verified }]

end VG.Artifacts.Ed25519MulAdd.AArch64
