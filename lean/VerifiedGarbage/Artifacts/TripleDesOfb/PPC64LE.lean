module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-OFB on PPC64LE -/

namespace VG.Artifacts.TripleDesOfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.TripleDes.ofbApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.ofb
    verified := Proof.TripleDes.PPC64LE.Scrub.ofb_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.ofbFinal
    verified := Proof.TripleDes.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesOfb.PPC64LE
