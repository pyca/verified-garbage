module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cbc
import VerifiedGarbage.Proof.Blowfish.X86.Scrub
import VerifiedGarbage.Impl.Blowfish.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideVerified
import VerifiedGarbage.Impl.Blowfish.X86.Ssse3Wide
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CBC on x86 -/

namespace VG.Artifacts.BlowfishCbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Fn.cbcEncryptChained
    verified := Proof.Blowfish.X86.Ssse3.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cbcEncryptChained
    verified := Proof.Blowfish.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Wide.Fn.cbcDecryptChained
    verified := Proof.Blowfish.X86.Ssse3.Wide.cbcDecryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cbcDecryptChained
    verified := Proof.Blowfish.X86.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishCbc.X86
