module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit

/-! # SM4-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.AArch64

def artifacts : List Artifact := [
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

end VG.Artifacts.Sm4Ofb.AArch64
