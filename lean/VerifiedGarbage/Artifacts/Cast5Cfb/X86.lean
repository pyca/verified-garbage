module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit

/-! # CAST5-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbEncrypt
    verified := Proof.Cast5.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbDecrypt
    verified := Proof.Cast5.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbEncryptFinal
    verified := Proof.Cast5.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbDecryptFinal
    verified := Proof.Cast5.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.Cast5Cfb.X86
