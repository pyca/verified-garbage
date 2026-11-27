module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Impl.Camellia.X86_64.Fn
import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
import VerifiedGarbage.Proof.Camellia.X86_64.CtrFinal
import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CTR on x86-64 -/

namespace VG.Artifacts.CamelliaCtr.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Camellia.ctrApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ctr, verified := Proof.Camellia.X86_64.Scrub.ctr_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ctr_spSafe },
  Spec.Camellia.ctrFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.ctrFinal, verified := Proof.Camellia.X86_64.Scrub.ctrFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.ctrFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.CamelliaCtr.X86_64
