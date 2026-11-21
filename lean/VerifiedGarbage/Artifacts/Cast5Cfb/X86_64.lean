module

public import VerifiedGarbage.Impl.Cast5.X86_64.Fn
public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbEncrypt, verified := .scrubbed Proof.Cast5.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Cast5.cfbDecryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbDecrypt, verified := .scrubbed Proof.Cast5.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbEncryptFinal, verified := .scrubbed Proof.Cast5.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbDecryptFinal, verified := .scrubbed Proof.Cast5.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.Cast5Cfb.X86_64
