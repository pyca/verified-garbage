module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Proof.Cast5.X86.Scrub
import VerifiedGarbage.Impl.Cast5.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
import VerifiedGarbage.Impl.Cast5.X86.Ssse3
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideVerified
import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CBC on x86 -/

namespace VG.Artifacts.Cast5Cbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cbcEncryptChained
    verified := Proof.Cast5.X86.Ssse3.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cbcEncryptChained
    verified := Proof.Cast5.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Wide.Fn.cbcDecryptChained
    verified := Proof.Cast5.X86.Ssse3.Wide.cbcDecryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cbcDecryptChained
    verified := Proof.Cast5.X86.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cbc.X86
