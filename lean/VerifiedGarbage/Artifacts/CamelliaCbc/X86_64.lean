module

public import VerifiedGarbage.Impl.Camellia.X86_64.Fn
public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit

/-! # Camellia-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cbcEncrypt, verified := .scrubbed Proof.Camellia.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cbcDecrypt, verified := .scrubbed Proof.Camellia.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cbcDecrypt_spSafe }]

end VG.Artifacts.CamelliaCbc.X86_64
