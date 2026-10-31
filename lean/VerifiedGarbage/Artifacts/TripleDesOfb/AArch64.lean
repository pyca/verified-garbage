module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.ofb
    stack := 1008
    verified := Proof.TripleDes.AArch64.ofb_framed }]

end VG.Artifacts.TripleDesOfb.AArch64
