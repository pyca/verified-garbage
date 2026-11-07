module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit

/-! # Camellia-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofb
    stack := 3344
    verified := Proof.Camellia.AArch64.ofb_framed },
  Spec.Camellia.ofbFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofbFinal
    stack := 3344
    verified := Proof.Camellia.AArch64.ofbFinal_framed }]

end VG.Artifacts.CamelliaOfb.AArch64
