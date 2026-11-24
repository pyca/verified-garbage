module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Scrub
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Proof.CmacTripleDes.X86.Ssse3Verified
public import VerifiedGarbage.Impl.CmacTripleDes.X86.Ssse3
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86.Ssse3Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.CmacTripleDes.X86
