module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.expandKey
    verified := Proof.Sm4.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Sm4.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Sm4.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Sm4.PPC64LE
