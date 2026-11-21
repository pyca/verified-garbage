module

public import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbEncrypt, verified := .scrubbed Proof.Blowfish.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Blowfish.cfbDecryptApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbDecrypt, verified := .scrubbed Proof.Blowfish.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbEncryptFinal, verified := .scrubbed Proof.Blowfish.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.cfbDecryptFinal, verified := .scrubbed Proof.Blowfish.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.BlowfishCfb.X86_64
