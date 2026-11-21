module

public import VerifiedGarbage.Impl.Cast5.X86_64.Fn
public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cbcEncryptChained, verified := .scrubbed Proof.Cast5.X86_64.Scrub.cbcEncryptChained_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cbcEncryptChained_spSafe },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cbcDecryptChained, verified := .scrubbed Proof.Cast5.X86_64.Scrub.cbcDecryptChained_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cbcDecryptChained_spSafe }]

end VG.Artifacts.Cast5Cbc.X86_64
