module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4 artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r5 402 Impl.Sm4.PPC64LE.expandKey
    stack := 3248
    verified := Proof.Sm4.PPC64LE.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .encrypt)
    stack := 3248
    verified := Proof.Sm4.PPC64LE.ecb_framed .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .decrypt)
    stack := 3248
    verified := Proof.Sm4.PPC64LE.ecb_framed .decrypt }]

end VG.Artifacts.Sm4.PPC64LE
