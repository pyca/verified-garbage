module

public import VerifiedGarbage.Impl.Sm4.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit

/-! # SM4-CFB128 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbEncrypt, verified := .scrubbed Proof.Sm4.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Sm4.cfbDecryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbDecrypt, verified := .scrubbed Proof.Sm4.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Sm4.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbEncryptFinal, verified := .scrubbed Proof.Sm4.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Sm4.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbDecryptFinal, verified := .scrubbed Proof.Sm4.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.Sm4Cfb.X86_64
