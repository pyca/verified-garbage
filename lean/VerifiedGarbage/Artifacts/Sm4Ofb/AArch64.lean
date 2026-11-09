module

public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit

/-! # SM4-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ofb
    stack := 3264
    verified := Proof.Sm4.AArch64.ofb_framed },
  Spec.Sm4.ofbFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ofbFinal
    stack := 3264
    verified := Proof.Sm4.AArch64.ofbFinal_framed }]

end VG.Artifacts.Sm4Ofb.AArch64
