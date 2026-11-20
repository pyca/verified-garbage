module

public import VerifiedGarbage.Proof.AesXts.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesXts.PPC64LE

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LE.Fn.encryptUnit
    verified := .scrubbed Proof.AesXts.PPC64LE.Scrub.encryptUnit_scrubbed },
  Spec.Xts.aesDecryptUnitApi.artifact PPC64LE.target {
    code := Impl.AesXts.PPC64LE.Fn.decryptUnit
    verified := .scrubbed Proof.AesXts.PPC64LE.Scrub.decryptUnit_scrubbed }]

end VG.Artifacts.AesXts.PPC64LE
