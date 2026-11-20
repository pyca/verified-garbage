module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-CTR on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ctr
    verified := .scrubbed Proof.Sm4.PPC64LE.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ctrFinal
    verified := .scrubbed Proof.Sm4.PPC64LE.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.Sm4Ctr.PPC64LE
