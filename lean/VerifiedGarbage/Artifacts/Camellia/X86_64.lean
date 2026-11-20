module

public import VerifiedGarbage.Impl.Camellia.X86_64.Fn
public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Camellia on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.expandKey, verified := .scrubbed Proof.Camellia.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.expandKey_spSafe },
  Spec.Camellia.ecbEncryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ecbEncrypt, verified := .scrubbed Proof.Camellia.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Camellia.ecbDecryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ecbDecrypt, verified := .scrubbed Proof.Camellia.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ecbDecrypt_spSafe }]

end VG.Artifacts.Camellia.X86_64
