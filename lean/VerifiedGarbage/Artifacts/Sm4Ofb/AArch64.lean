module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Impl.Sm4.AArch64.Fn
import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-OFB on AArch64 -/

namespace VG.Artifacts.Sm4Ofb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Sm4.ofbApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ofbSm4
    verified := Proof.Sm4.AArch64.ModesResidue.ofbSm4Code_scrubbed },
  Spec.Sm4.ofbApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ofb
    verified := Proof.Sm4.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ofbFinalSm4
    verified := Proof.Sm4.AArch64.ModesResidue.ofbFinalSm4Code_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ofbFinal
    verified := Proof.Sm4.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Ofb.AArch64
