module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CFB64 on x86-64 -/

namespace VG.Artifacts.BlowfishCfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Blowfish.cfbEncryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbEncrypt, verified := Proof.Blowfish.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Blowfish.cfbDecryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbDecrypt, verified := Proof.Blowfish.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbEncryptFinal, verified := Proof.Blowfish.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbDecryptFinal, verified := Proof.Blowfish.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbDecryptFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.BlowfishCfb.X86_64
