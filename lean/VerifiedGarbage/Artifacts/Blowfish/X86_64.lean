module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # Blowfish on x86-64 -/

namespace VG.Artifacts.Blowfish.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Blowfish.expandKeyApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.expandKey, verified := Proof.Blowfish.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.expandKey_spSafe },
  Spec.Blowfish.ecbEncryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ecbEncrypt, verified := Proof.Blowfish.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Blowfish.ecbDecryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ecbDecrypt, verified := Proof.Blowfish.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ecbDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.Blowfish.X86_64
