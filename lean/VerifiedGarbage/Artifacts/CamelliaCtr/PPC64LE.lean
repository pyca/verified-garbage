module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CTR on PPC64LE -/

namespace VG.Artifacts.CamelliaCtr.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Camellia.ctrApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ctr
    verified := Proof.Camellia.PPC64LE.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ctrFinal
    verified := Proof.Camellia.PPC64LE.Scrub.ctrFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCtr.PPC64LE
