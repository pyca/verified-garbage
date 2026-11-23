module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # CAST5 (RFC 2144) on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.expandKey
    verified := Proof.Cast5.X86.Scrub.expandKey_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.ecbEncrypt
    verified := Proof.Cast5.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.ecbDecrypt
    verified := Proof.Cast5.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Cast5.X86
