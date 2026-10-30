module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CFB128 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncrypt
    stack := 3408
    verified := Proof.Camellia.PPC64LE.cfbEnc_framed Proof.Camellia.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Camellia.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecrypt
    stack := 3408
    verified := Proof.Camellia.PPC64LE.cfbDec_framed Proof.Camellia.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.CamelliaCfb.PPC64LE
