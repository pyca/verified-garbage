module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideVerified
public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideLit

/-! # CAST5-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86

def artifacts : List (Artifact X86.target) := [
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cfbEncrypt
    verified := Proof.Cast5.X86.Ssse3.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbEncrypt
    verified := Proof.Cast5.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Wide.Fn.cfbDecrypt
    verified := Proof.Cast5.X86.Ssse3.Wide.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbDecrypt
    verified := Proof.Cast5.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cfbEncryptFinal
    verified := Proof.Cast5.X86.Ssse3.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbEncryptFinal
    verified := Proof.Cast5.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cfbDecryptFinal
    verified := Proof.Cast5.X86.Ssse3.cfbDecryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbDecryptFinal
    verified := Proof.Cast5.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.Cast5Cfb.X86
