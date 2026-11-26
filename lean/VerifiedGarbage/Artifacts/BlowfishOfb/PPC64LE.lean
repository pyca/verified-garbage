module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-OFB on PPC64LE -/

namespace VG.Artifacts.BlowfishOfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Blowfish.ofbApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.ofb
    verified := Proof.Blowfish.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Blowfish.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.ofbFinal
    verified := Proof.Blowfish.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishOfb.PPC64LE
