module

public import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cbcEncrypt, verified := Proof.Blowfish.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cbcDecrypt, verified := Proof.Blowfish.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cbcDecrypt_spSafe }]

end VG.Artifacts.BlowfishCbc.X86_64
