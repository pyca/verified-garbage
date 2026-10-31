module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit

/-! # Blowfish-CFB64 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt
    stack := 128
    verified := Proof.Blowfish.PPC64LE.cfbEnc_framed Proof.Blowfish.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Blowfish.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt
    stack := 128
    verified := Proof.Blowfish.PPC64LE.cfbDec_framed Proof.Blowfish.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.BlowfishCfb.PPC64LE
