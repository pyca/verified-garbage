module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
public import VerifiedGarbage.Proof.MlKem.X86_64.Sample16
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified16
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-KEM (FIPS 203) on x86-64: the polynomial primitives -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact := [
  Spec.MlKem.checkEkApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.checkEk
    verified := Proof.MlKem.X86_64.checkEk_verified },
  Spec.MlKem.checkEkApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlKem.X86_64.checkEkAvx2
    verified := Proof.MlKem.X86_64.checkEkAvx2_verified
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlKem.X86_64
