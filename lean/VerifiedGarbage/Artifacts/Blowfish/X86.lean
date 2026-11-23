module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
import VerifiedGarbage.Proof.Blowfish.X86.Lit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit

/-! # Blowfish on x86 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Fn.expandKey
    verified := Proof.Blowfish.X86.Ssse3.expandKey_scrubbed },
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.expandKey
    verified := Proof.Blowfish.X86.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ecbEncrypt
    verified := Proof.Blowfish.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ecbDecrypt
    verified := Proof.Blowfish.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Blowfish.X86
