module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # ML-DSA (FIPS 204) signing on x86 -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.X86

open VG.Proof.MlDsa.X86.Sign (prims)

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44")
      (Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa44)
    stack := 136
    verified := Proof.MlDsa.X86.Message.sign44_verified },
  Spec.MlDsa.sign65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65")
      (Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa65)
    stack := 136
    verified := Proof.MlDsa.X86.Message.sign65_verified },
  Spec.MlDsa.sign87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87")
      (Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa87)
    stack := 136
    verified := Proof.MlDsa.X86.Message.sign87_verified }]

end VG.Artifacts.MlDsaSign.X86
