module

public import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit

public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.expandKey, verified := Proof.Blowfish.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.expandKey_spSafe },
  Spec.Blowfish.ecbEncryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ecbEncrypt, verified := Proof.Blowfish.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Blowfish.ecbDecryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ecbDecrypt, verified := Proof.Blowfish.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ecbDecrypt_spSafe }]

end VG.Artifacts.Blowfish.X86_64
