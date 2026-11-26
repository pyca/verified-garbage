module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-OFB on AArch64 -/

namespace VG.Artifacts.TripleDesOfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.TripleDes.ofbApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.ofb
    verified := Proof.TripleDes.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.ofbFinal
    verified := Proof.TripleDes.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesOfb.AArch64
