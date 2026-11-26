module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Impl.TripleDes.X86.Fn
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.CbcLit
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CBC on x86 -/

namespace VG.Artifacts.TripleDesCbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.cbcEncryptChained
    verified := Proof.TripleDes.X86.Ssse3.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cbcEncryptChained
    verified := Proof.TripleDes.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cbcDecryptChained
    verified := Proof.TripleDes.X86.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCbc.X86
