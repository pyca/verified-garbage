module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.X86.Scrub
import VerifiedGarbage.Impl.Sm3.X86.Stream
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm3.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM3 (GB/T 32905-2016) on x86 -/

namespace VG.Artifacts.Sm3.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Sm3.initApi.artifact X86.target {
    code := Impl.Sm3.X86.Fn.init
    verified := Proof.Sm3.X86.Scrub.init_scrubbed },
  Spec.Sm3.updateApi.artifact X86.target {
    code := Impl.Sm3.X86.Fn.update
    verified := Proof.Sm3.X86.Scrub.update_scrubbed },
  Spec.Sm3.finalizeApi.artifact X86.target {
    code := Impl.Sm3.X86.Fn.finalize
    verified := Proof.Sm3.X86.Scrub.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm3.X86
