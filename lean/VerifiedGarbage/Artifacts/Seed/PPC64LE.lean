module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit

/-! # SEED on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Seed.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.expandKey
    verified := Proof.Seed.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Seed.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Seed.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Seed.PPC64LE
