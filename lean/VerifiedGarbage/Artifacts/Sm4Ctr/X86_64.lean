module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
import VerifiedGarbage.Impl.Sm4.X86_64.Fn
import VerifiedGarbage.Proof.Sm4.X86_64.CtrVerified
import VerifiedGarbage.Proof.Sm4.X86_64.CtrFinal
import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CTR on x86-64 -/

namespace VG.Artifacts.Sm4Ctr.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sm4.ctrApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ctr, verified := Proof.Sm4.X86_64.Scrub.ctr_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ctr_spSafe },
  Spec.Sm4.ctrFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.ctrFinal, verified := Proof.Sm4.X86_64.Scrub.ctrFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.ctrFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sm4Ctr.X86_64
