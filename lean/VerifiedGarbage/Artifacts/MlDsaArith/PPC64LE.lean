module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.NttInv
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: the arithmetic of polynomials -/

@[expose] public section

namespace VG.Artifacts.MlDsaArith.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.nttApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Arith.ntt
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Arith.Ntt.verified },
  Spec.MlDsa.nttInvApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Arith.nttInv
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Arith.NttInv.verified },
  Spec.MlDsa.mulApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Arith.mul
    verified := Proof.MlDsa.PPC64LE.Arith.Mul.mul_verified },
  Spec.MlDsa.mulAddApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Arith.mulAdd
    verified := Proof.MlDsa.PPC64LE.Arith.Mul.mulAdd_verified },
  Spec.MlDsa.addApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Arith.add
    verified := Proof.MlDsa.PPC64LE.Arith.AddSub.add_verified },
  Spec.MlDsa.subApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Arith.sub
    verified := Proof.MlDsa.PPC64LE.Arith.AddSub.sub_verified }]

end VG.Artifacts.MlDsaArith.PPC64LE
