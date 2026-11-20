module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CTR on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ctr
    verified := .scrubbed Proof.Camellia.PPC64LE.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ctrFinal
    verified := .scrubbed Proof.Camellia.PPC64LE.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.CamelliaCtr.PPC64LE
