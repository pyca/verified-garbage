module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! The merged scalar multiply-add API, implemented with baseline integer instructions. -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.AArch64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarMulAddApi with
    target := AArch64.target
    doc := Spec.Ed25519.scalarMulAddApi.doc (notes := ["Computes the complete 512-bit \
      multiply-add before reducing it modulo the subgroup order a 64-bit word at a time. All three input scalars \
      may use all 256 bits. The function saves callee-saved registers in `scratch`."])
    code := Impl.Ed25519.AArch64.scalarMulAdd
    contract := Spec.Ed25519.scalarMulAddContract AArch64.abi
    verified := Proof.Ed25519.AArch64.scalarMulAdd_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519MulAdd.AArch64
