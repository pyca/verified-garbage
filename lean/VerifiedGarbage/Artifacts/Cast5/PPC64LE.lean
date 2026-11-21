module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit

/-! # CAST5 (RFC 2144) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.expandKey
    verified := Proof.Cast5.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Cast5.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Cast5.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Cast5.PPC64LE
