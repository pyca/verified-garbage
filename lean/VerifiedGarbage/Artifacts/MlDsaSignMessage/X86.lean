module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
public import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
public import VerifiedGarbage.Proof.MlKem.X86.EncV
public import VerifiedGarbage.Proof.MlKem.X86.NttSetup
public import VerifiedGarbage.Proof.MlKem.X86.Table
public import VerifiedGarbage.TCB.X86.Print

/-! # ML-DSA (FIPS 204) on x86 (32-bit): signing messages, with encoded and prepared keys -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.X86

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44")
        (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44)) Spec.MlDsa.mlDsa44
    stack := 176
    verified := Proof.MlDsa.X86.Message.signMessage44_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa44")
      (Impl.MlDsa.X86.Sign.signPrepared Spec.MlDsa.mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44")
        (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44)) Spec.MlDsa.mlDsa44
    stack := 176
    verified := Proof.MlDsa.X86.Message.signMessagePrepared44_verified },
  Spec.MlDsa.signMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65")
        (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65)) Spec.MlDsa.mlDsa65
    stack := 176
    verified := Proof.MlDsa.X86.Message.signMessage65_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa65")
      (Impl.MlDsa.X86.Sign.signPrepared Spec.MlDsa.mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65")
        (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65)) Spec.MlDsa.mlDsa65
    stack := 176
    verified := Proof.MlDsa.X86.Message.signMessagePrepared65_verified },
  Spec.MlDsa.signMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87")
        (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87)) Spec.MlDsa.mlDsa87
    stack := 176
    verified := Proof.MlDsa.X86.Message.signMessage87_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa87")
      (Impl.MlDsa.X86.Sign.signPrepared Spec.MlDsa.mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87")
        (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87)) Spec.MlDsa.mlDsa87
    stack := 176
    verified := Proof.MlDsa.X86.Message.signMessagePrepared87_verified }]

end VG.Artifacts.MlDsaSignMessage.X86
