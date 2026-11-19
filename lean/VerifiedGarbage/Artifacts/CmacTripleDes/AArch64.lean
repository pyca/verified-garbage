module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Scrub
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.AArch64

open VG.Proof.CmacTripleDes.AArch64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.streamInit
    verified := Proof.CmacTripleDes.Stream.AArch64.init_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
       .v26, .v27, .v28, .v29, .v30, .v31],
       []⟩ (Proof.CmacTripleDes.AArch64.Scrub.initOk 640)),
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x4 Impl.CmacTripleDes.Stream.AArch64.absorb
    verified := Proof.CmacTripleDes.Stream.AArch64.absorb_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
       .v26, .v27, .v28, .v29, .v30, .v31],
       []⟩ (Proof.CmacTripleDes.AArch64.Scrub.absorbOk 688)),
  Spec.Cmac.tdesFinishApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.finish
    verified := Proof.CmacTripleDes.Stream.AArch64.finish_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
       .v26, .v27, .v28, .v29, .v30, .v31],
       []⟩ (Proof.CmacTripleDes.AArch64.Scrub.finishOk 640))]

end VG.Artifacts.CmacTripleDes.AArch64
