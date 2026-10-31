module

public import VerifiedGarbage.Proof.Sm4.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x2 396 Impl.Sm4.AArch64.expandKey
    stack := 3168
    verified := Proof.Sm4.AArch64.expandKey_framed },
  Spec.Sm4.ecbDirApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ecbAnyFramed
    stack := 3168
    verified := Proof.Sm4.AArch64.ecbAny_framed },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.ecbCall .encrypt Proof.Sm4.AArch64.ecbAnyFramed
    stack := 3184
    verified := Proof.Sm4.AArch64.ecbCall_verified .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.ecbCall .decrypt Proof.Sm4.AArch64.ecbAnyFramed
    stack := 3184
    verified := Proof.Sm4.AArch64.ecbCall_verified .decrypt },
  (Spec.Sm4.Prepared.prepareApi Impl.Sm4.AArch64.layout).artifact AArch64.target {
    code := Impl.Sm4.AArch64.prepareKeys
    verified := Proof.Sm4.AArch64.prepare_verified },
  (Spec.Sm4.Prepared.cryptApi Impl.Sm4.AArch64.layout).artifact AArch64.target {
    code := Impl.Sm4.AArch64.cryptPrepared
    verified := Proof.Sm4.AArch64.crypt_verified }]

end VG.Artifacts.Sm4.AArch64
