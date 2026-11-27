module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Scrub
import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
import VerifiedGarbage.Proof.CmacTripleDes.X86.Ssse3Verified
import VerifiedGarbage.Impl.CmacTripleDes.X86.Ssse3
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86 -/

namespace VG.Artifacts.CmacTripleDes.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Cmac.tdesStreamInitApi.artifact X86.target {
    code := Impl.CmacTripleDes.Stream.X86.Fn.init
    verified := Proof.CmacTripleDes.Stream.X86.Scrub.init_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.CmacTripleDes.X86.Ssse3.Fn.absorb
    verified := Proof.CmacTripleDes.X86.Ssse3.absorb_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact X86.target {
    code := Impl.CmacTripleDes.Stream.X86.Fn.absorb
    verified := Proof.CmacTripleDes.Stream.X86.Scrub.absorb_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.CmacTripleDes.X86.Ssse3.Fn.finish
    verified := Proof.CmacTripleDes.X86.Ssse3.finish_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact X86.target {
    code := Impl.CmacTripleDes.Stream.X86.Fn.finish
    verified := Proof.CmacTripleDes.Stream.X86.Scrub.finish_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CmacTripleDes.X86
