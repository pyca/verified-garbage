module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CTR on PPC64LE -/

namespace VG.Artifacts.Sm4Ctr.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sm4.ctrApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ctr
    verified := Proof.Sm4.PPC64LE.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ctrFinal
    verified := Proof.Sm4.PPC64LE.Scrub.ctrFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Ctr.PPC64LE
