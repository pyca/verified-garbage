module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-OFB on PPC64LE -/

namespace VG.Artifacts.CamelliaOfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Camellia.ofbApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ofb
    verified := Proof.Camellia.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ofbFinal
    verified := Proof.Camellia.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaOfb.PPC64LE
