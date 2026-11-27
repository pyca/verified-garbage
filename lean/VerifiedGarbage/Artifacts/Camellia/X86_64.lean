module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Impl.Camellia.X86_64.Fn
import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia on x86-64 -/

namespace VG.Artifacts.Camellia.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Camellia.expandKeyApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.expandKey, verified := Proof.Camellia.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.expandKey_spSafe },
  Spec.Camellia.ecbEncryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ecbEncrypt, verified := Proof.Camellia.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Camellia.ecbDecryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ecbDecrypt, verified := Proof.Camellia.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ecbDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.Camellia.X86_64
