module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-CFB128 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncrypt
    stack := 3296
    verified := Proof.Sm4.PPC64LE.cfbEnc_framed Proof.Sm4.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Sm4.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecrypt
    stack := 3296
    verified := Proof.Sm4.PPC64LE.cfbDec_framed Proof.Sm4.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.Sm4Cfb.PPC64LE
