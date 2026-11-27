module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.Proof.Zeroize.X86
import VerifiedGarbage.Proof.Zeroize.X86Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Zeroize.Common32
import VerifiedGarbage.Impl.Zeroize.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Zeroization on x86 -/

namespace VG.Artifacts.Zeroize.X86
open VG.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.X86.Fn.zeroize
    verified := Proof.Zeroize.X86.zeroize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Zeroize.X86
