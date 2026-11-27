module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Impl.Cast5.AArch64.Fn
import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.AArch64.FbResidue
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-OFB on AArch64 -/

namespace VG.Artifacts.Cast5Ofb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Cast5.ofbApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.ofb
    verified := Proof.Cast5.AArch64.FbResidue.ofbCode_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.ofbFinal
    verified := Proof.Cast5.AArch64.FbResidue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Ofb.AArch64
