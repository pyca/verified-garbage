module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Blowfish on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blowfish.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.expandKey
    verified := Proof.Blowfish.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Blowfish.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Blowfish.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Blowfish.PPC64LE
