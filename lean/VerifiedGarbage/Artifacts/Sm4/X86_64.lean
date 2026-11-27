module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Impl.Sm4.X86_64.Fn
import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
import VerifiedGarbage.Proof.Sm4.X86_64.PreparedVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4 on x86-64 -/

namespace VG.Artifacts.Sm4.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sm4.expandKeyApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.expandKey, verified := Proof.Sm4.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.expandKey_spSafe },
  Spec.Sm4.ecbEncryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ecbEncrypt, verified := Proof.Sm4.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Sm4.ecbDecryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ecbDecrypt, verified := Proof.Sm4.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ecbDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sm4.X86_64
