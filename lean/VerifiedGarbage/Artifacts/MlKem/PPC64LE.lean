module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.MlKem.PPC64LE.NttInv
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Mul
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on PPC64LE: the arithmetic of polynomials -/

@[expose] public section

namespace VG.Artifacts.MlKem.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem.nttApi.artifact PPC64LE.target {
    notes := ["The function uses no stack: it saves `r14` and `r15` in `scratch`."]
    code := Impl.MlKem.PPC64LE.ntt
    verified := Proof.MlKem.PPC64LE.Ntt.verified },
  Spec.MlKem.nttInvApi.artifact PPC64LE.target {
    notes := ["The function uses no stack: it saves `r14` and `r15` in `scratch`."]
    code := Impl.MlKem.PPC64LE.nttInv
    verified := Proof.MlKem.PPC64LE.NttInv.verified },
  Spec.MlKem.mulApi.artifact PPC64LE.target {
    notes := ["The function uses no stack: it saves `r14` and `r15` in `scratch`."]
    code := Impl.MlKem.PPC64LE.multiplyNTTs
    verified := Proof.MlKem.PPC64LE.Mul.verified },
  Spec.MlKem.addApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.add
    verified := Proof.MlKem.PPC64LE.Add.add_verified },
  Spec.MlKem.subApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.sub
    verified := Proof.MlKem.PPC64LE.Add.sub_verified }]

end VG.Artifacts.MlKem.PPC64LE
