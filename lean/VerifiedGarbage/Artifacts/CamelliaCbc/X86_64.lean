module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Impl.Camellia.X86_64.Fn
import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CBC on x86-64 -/

namespace VG.Artifacts.CamelliaCbc.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cbcEncrypt, verified := Proof.Camellia.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cbcDecrypt, verified := Proof.Camellia.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cbcDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.CamelliaCbc.X86_64
