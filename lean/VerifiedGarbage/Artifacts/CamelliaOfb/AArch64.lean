module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofb
    stack := 3344
    verified := Proof.Camellia.AArch64.ofb_framed }]

end VG.Artifacts.CamelliaOfb.AArch64
