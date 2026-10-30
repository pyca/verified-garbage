module

public import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit

/-! # SM4-GCM on baseline AArch64: its counter mode and key setup

The functions that call GHASH are generic over its implementations
(`Generic/Sm4Gcm/AArch64/Sm4Gcm.lean`). -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ctr32
    stack := 3264
    verified := Proof.Sm4.AArch64.ctr32_framed },
  Spec.Sm4.Gcm.initApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x2 Impl.Sm4Gcm.AArch64.init
    stack := 4032
    verified := Proof.Sm4Gcm.AArch64.init_framed }]

end VG.Artifacts.Sm4Gcm.AArch64
