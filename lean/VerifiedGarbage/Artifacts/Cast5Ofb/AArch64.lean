module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact AArch64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofb
    stack := 112
    verified := Proof.Cast5.AArch64.ofb_framed }]

end VG.Artifacts.Cast5Ofb.AArch64
