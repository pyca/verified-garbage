module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-OFB on PPC64LE -/

namespace VG.Artifacts.Cast5Ofb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cast5.ofbApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ofb
    verified := Proof.Cast5.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ofbFinal
    verified := Proof.Cast5.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Ofb.PPC64LE
