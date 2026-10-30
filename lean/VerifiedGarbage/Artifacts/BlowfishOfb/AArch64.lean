module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.ofb
    stack := 224
    verified := Proof.Blowfish.AArch64.ofb_framed }]

end VG.Artifacts.BlowfishOfb.AArch64
