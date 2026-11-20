module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.Lit

/-! # SM4 on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4.X86

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.expandKey
    verified := .scrubbed Proof.Sm4.X86.Scrub.expandKey_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ecbEncrypt
    verified := .scrubbed Proof.Sm4.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ecbDecrypt
    verified := .scrubbed Proof.Sm4.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Sm4.X86
