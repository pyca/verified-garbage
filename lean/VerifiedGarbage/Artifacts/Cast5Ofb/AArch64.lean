module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # CAST5-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofb
    stack := 112
    verified := Proof.Cast5.ofb_keyed Proof.Cast5.AArch64.ofb_framed },
  Spec.Cast5.ofbFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofbFinal
    stack := 112
    verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.AArch64.ofbFinal_framed }]

end VG.Artifacts.Cast5Ofb.AArch64
