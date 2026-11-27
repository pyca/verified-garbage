module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Impl.Sm4.X86_64.Fn
import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CBC on x86-64 -/

namespace VG.Artifacts.Sm4Cbc.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cbcEncrypt, verified := Proof.Sm4.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cbcDecrypt, verified := Proof.Sm4.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cbcDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sm4Cbc.X86_64
