module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.FbLit
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit

/-! # Camellia-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.cfbEncrypt
    verified := Proof.Camellia.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.cfbDecrypt
    verified := Proof.Camellia.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.cfbEncryptFinal
    verified := Proof.Camellia.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.cfbDecryptFinal
    verified := Proof.Camellia.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.CamelliaCfb.X86
