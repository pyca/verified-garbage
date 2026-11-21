module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit

/-! # CAST5-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ofb
    verified := .scrubbed Proof.Cast5.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.ofbFinal
    verified := .scrubbed Proof.Cast5.PPC64LE.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.Cast5Ofb.PPC64LE
