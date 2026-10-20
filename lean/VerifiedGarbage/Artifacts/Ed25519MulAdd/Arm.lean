module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact Arm.target {
    notes := ["Computes the complete 512-bit \
      multiply-add before reducing modulo the subgroup order. All three input scalars \
      may use all 256 bits. Multiplication uses only the low 32-bit `mul` instruction \
      on 16-bit limbs. Callee-saved registers are saved in `scratch`."]
    code := Impl.Ed25519.Arm.scalarMulAdd
    verified := Proof.Ed25519.Arm.scalarMulAdd_verified
    stack := 0 }]

end VG.Artifacts.Ed25519MulAdd.Arm
