module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit

/-! # CAST5-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.PPC64LE

def artifacts : List Artifact := [
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

end VG.Artifacts.Cast5Cfb.PPC64LE
