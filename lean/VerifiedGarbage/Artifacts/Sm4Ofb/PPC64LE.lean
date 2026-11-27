module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-OFB on PPC64LE -/

namespace VG.Artifacts.Sm4Ofb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sm4.ofbApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ofb
    verified := Proof.Sm4.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.ofbFinal
    verified := Proof.Sm4.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Ofb.PPC64LE
