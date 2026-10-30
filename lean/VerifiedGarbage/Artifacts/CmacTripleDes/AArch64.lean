module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64

The functions call nothing: the return address stays in `x30`. They keep
their working space in a frame of their own on the stack
(`Proof/CmacTripleDes/Stream/AArch64/Frame.lean`).
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.AArch64

open VG.Proof.CmacTripleDes.AArch64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.streamInit
    stack := 640
    verified := Proof.CmacTripleDes.Stream.AArch64.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x4 Impl.CmacTripleDes.Stream.AArch64.absorb
    stack := 688
    verified := Proof.CmacTripleDes.Stream.AArch64.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.finish
    stack := 640
    verified := Proof.CmacTripleDes.Stream.AArch64.finish_framed }]

end VG.Artifacts.CmacTripleDes.AArch64
