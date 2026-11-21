module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit

/-! # Blowfish-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Blowfish.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Blowfish.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Blowfish.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Blowfish.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Blowfish.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.BlowfishCfb.PPC64LE
