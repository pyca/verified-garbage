module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrScrub

/-! # SM4-CTR on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := "_sm4"
    code := Impl.StackScratch.AArch64.withStackScratch 224 .x4 Impl.Sm4.AArch64.Sm4e.ctr
    verified := Proof.Sm4.AArch64.Sm4e.ctr_framed }
      ⟨[.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23],
       []⟩ (Proof.Sm4.AArch64.CtrScrub.ctrOk 224)),
  Spec.Sm4.ctrApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 3264 .x4 Impl.Sm4.AArch64.ctr
    verified := Proof.Sm4.AArch64.ctr_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
       .v27, .v28, .v29, .v30, .v31],
       []⟩ (Proof.Sm4.AArch64.CtrScrub.ctrOk 3264))] ++
  Proof.Variants.Sm4Ctr.AArch64.variants.attach.map
      fun (v : { v : Proof.Sm4.AArch64.CtrFinal.CtrImpl // v ∈ Proof.Variants.Sm4Ctr.AArch64.variants }) =>
    Spec.Sm4.ctrFinalApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 (Impl.Sm4.AArch64.ctrFinal v.1.name v.1.code)
      verified := Proof.Sm4.AArch64.CtrFinal.ctrFinal_framed v.1 }
      (AArch64.ScrubAll.clearUnion Proof.Sm4.AArch64.CtrScrub.ctrFinalOwn v.1.clear)
      Proof.Sm4.AArch64.CtrScrub.ctrFinalOk (Proof.Sm4.AArch64.CtrScrub.ctrFinalSide v.1 v.2))

end VG.Artifacts.Sm4Ctr.AArch64
