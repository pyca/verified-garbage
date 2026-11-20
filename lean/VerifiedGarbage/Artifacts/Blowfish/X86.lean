module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.Lit

/-! # Blowfish on x86 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.expandKey
    verified := .scrubbed Proof.Blowfish.X86.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ecbEncrypt
    verified := .scrubbed Proof.Blowfish.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ecbDecrypt
    verified := .scrubbed Proof.Blowfish.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Blowfish.X86
