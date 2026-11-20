module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86.FbLit

/-! # SM4-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbEncrypt
    verified := .scrubbed Proof.Sm4.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbDecrypt
    verified := .scrubbed Proof.Sm4.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Sm4.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Sm4.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.Sm4Cfb.X86
