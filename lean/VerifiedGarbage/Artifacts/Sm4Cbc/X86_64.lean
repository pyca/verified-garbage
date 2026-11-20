module

public import VerifiedGarbage.Impl.Sm4.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cbcEncrypt, verified := .scrubbed Proof.Sm4.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cbcDecrypt, verified := .scrubbed Proof.Sm4.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cbcDecrypt_spSafe }]

end VG.Artifacts.Sm4Cbc.X86_64
