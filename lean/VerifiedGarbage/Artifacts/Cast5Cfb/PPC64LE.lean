module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CFB64 on PPC64LE -/

namespace VG.Artifacts.Cast5Cfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cast5.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Cast5.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Cast5.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Cast5.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Cast5.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cfb.PPC64LE
