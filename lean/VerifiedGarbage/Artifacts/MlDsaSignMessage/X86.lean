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
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Proof.MlKem.X86.NttSetup
import VerifiedGarbage.Proof.MlKem.X86.Table

/-! # ML-DSA (FIPS 204) on x86 (32-bit): signing messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.X86

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage87_verified }]

end VG.Artifacts.MlDsaSignMessage.X86
