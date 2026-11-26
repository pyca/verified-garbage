module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Impl.Cast5.X86_64.Fn
import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CBC on x86-64 -/

namespace VG.Artifacts.Cast5Cbc.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cbcEncryptChained, verified := Proof.Cast5.X86_64.Scrub.cbcEncryptChained_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cbcEncryptChained_spSafe },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cbcDecryptChained, verified := Proof.Cast5.X86_64.Scrub.cbcDecryptChained_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cbcDecryptChained_spSafe }]

spec_apis artifacts

end VG.Artifacts.Cast5Cbc.X86_64
