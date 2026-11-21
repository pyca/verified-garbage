module

public import VerifiedGarbage.Impl.Sm4.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.Lit

/-! # SM4 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.expandKey, verified := Proof.Sm4.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.expandKey_spSafe },
  Spec.Sm4.ecbEncryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ecbEncrypt, verified := Proof.Sm4.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Sm4.ecbDecryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ecbDecrypt, verified := Proof.Sm4.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ecbDecrypt_spSafe }]

end VG.Artifacts.Sm4.X86_64
