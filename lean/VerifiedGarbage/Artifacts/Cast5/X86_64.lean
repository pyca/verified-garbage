module

public import VerifiedGarbage.Impl.Cast5.X86_64.Fn
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5 (RFC 2144) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.expandKey, verified := .scrubbed Proof.Cast5.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.expandKey_spSafe },
  Spec.Cast5.ecbEncryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ecbEncrypt, verified := .scrubbed Proof.Cast5.X86_64.Scrub.ecbEncrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ecbEncrypt_spSafe },
  Spec.Cast5.ecbDecryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ecbDecrypt, verified := .scrubbed Proof.Cast5.X86_64.Scrub.ecbDecrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ecbDecrypt_spSafe }]

end VG.Artifacts.Cast5.X86_64
