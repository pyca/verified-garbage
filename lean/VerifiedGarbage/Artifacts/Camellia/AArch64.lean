module

public import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Camellia.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x3 406 Impl.Camellia.AArch64.expandKey
    stack := 3248
    verified := Proof.Camellia.AArch64.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406
      (Impl.Camellia.AArch64.ecb .encrypt)
    stack := 3248
    verified := Proof.Camellia.AArch64.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406
      (Impl.Camellia.AArch64.ecb .decrypt)
    stack := 3248
    verified := Proof.Camellia.AArch64.ecb_framed .decrypt },
  (Spec.Camellia.Prepared.prepareApi Impl.Camellia.AArch64.layout).artifact AArch64.target {
    code := Impl.Camellia.AArch64.prepareKeys
    verified := Proof.Camellia.AArch64.prepare_verified },
  (Spec.Camellia.Prepared.cryptApi Impl.Camellia.AArch64.layout).artifact AArch64.target {
    code := Impl.Camellia.AArch64.cryptPrepared
    verified := Proof.Camellia.AArch64.crypt_verified }]

end VG.Artifacts.Camellia.AArch64
