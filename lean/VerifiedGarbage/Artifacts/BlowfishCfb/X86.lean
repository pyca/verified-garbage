module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit

/-! # Blowfish-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cfbEncrypt
    verified := Proof.Blowfish.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Blowfish.cfbDecryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cfbDecrypt
    verified := Proof.Blowfish.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cfbEncryptFinal
    verified := Proof.Blowfish.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cfbDecryptFinal
    verified := Proof.Blowfish.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.BlowfishCfb.X86
