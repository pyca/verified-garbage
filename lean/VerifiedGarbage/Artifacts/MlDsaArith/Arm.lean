module

public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on 32-bit ARM: the arithmetic of polynomials -/

@[expose] public section

namespace VG.Artifacts.MlDsaArith.Arm

def artifacts : List Artifact := [
  Spec.MlDsa.nttApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r10` on the stack (the 28 bytes below the stack pointer), and \
        stores a table of the 256 zetas in `scratch`."]
    code := Impl.MlDsa.Arm.Arith.ntt
    stack := 28
    verified := Proof.MlDsa.Arm.Arith.Ntt.verified },
  Spec.MlDsa.nttInvApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r10` on the stack (the 28 bytes below the stack pointer), and \
        stores a table of the 256 negated zetas in `scratch`."]
    code := Impl.MlDsa.Arm.Arith.nttInv
    stack := 28
    verified := Proof.MlDsa.Arm.Arith.NttInv.verified },
  Spec.MlDsa.mulApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r9` on the stack (the 24 bytes below the stack pointer)."]
    code := Impl.MlDsa.Arm.Arith.mul
    stack := 24
    verified := Proof.MlDsa.Arm.Arith.Mul.mul_verified },
  Spec.MlDsa.mulAddApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r9` on the stack (the 24 bytes below the stack pointer)."]
    code := Impl.MlDsa.Arm.Arith.mulAdd
    stack := 24
    verified := Proof.MlDsa.Arm.Arith.Mul.mulAdd_verified },
  Spec.MlDsa.addApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Arith.add
    verified := Proof.MlDsa.Arm.Arith.AddSub.add_verified },
  Spec.MlDsa.subApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Arith.sub
    verified := Proof.MlDsa.Arm.Arith.AddSub.sub_verified }]

end VG.Artifacts.MlDsaArith.Arm
