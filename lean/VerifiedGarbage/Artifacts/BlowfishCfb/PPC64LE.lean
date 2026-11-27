module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CFB64 on PPC64LE -/

namespace VG.Artifacts.BlowfishCfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
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

spec_apis artifacts

end VG.Artifacts.BlowfishCfb.PPC64LE
