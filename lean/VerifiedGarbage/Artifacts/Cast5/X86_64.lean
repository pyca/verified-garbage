module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Impl.Cast5.X86_64.Fn
import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5 (RFC 2144) on x86-64 -/

namespace VG.Artifacts.Cast5.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Cast5.expandKeyApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.expandKey, verified := Proof.Cast5.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.expandKey_spSafe },
  Spec.Cast5.ecbEncryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ecbEncrypt, verified := Proof.Cast5.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Cast5.ecbDecryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ecbDecrypt, verified := Proof.Cast5.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ecbDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.Cast5.X86_64
