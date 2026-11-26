module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cbc
import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CBC on x86-64 -/

namespace VG.Artifacts.BlowfishCbc.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cbcEncrypt, verified := Proof.Blowfish.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cbcDecrypt, verified := Proof.Blowfish.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cbcDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.BlowfishCbc.X86_64
