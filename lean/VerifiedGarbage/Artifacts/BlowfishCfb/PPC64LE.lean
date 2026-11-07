module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit

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
    verified := Proof.Blowfish.PPC64LE.cfbDec_framed Proof.Blowfish.PPC64LE.Modes.cfbDecrypt_verified },
  Spec.Blowfish.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncryptFinal
    stack := 128
    verified := Proof.Blowfish.PPC64LE.FbFinal.cfbEncryptFinal_framed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecryptFinal
    stack := 128
    verified := Proof.Blowfish.PPC64LE.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.BlowfishCfb.PPC64LE
