module

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
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.streamInit
    verified := Proof.CmacTripleDes.Stream.AArch64.init_framed } (Proof.CmacTripleDes.AArch64.Scrub.initOk 640)),
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x4 Impl.CmacTripleDes.Stream.AArch64.absorb
    verified := Proof.CmacTripleDes.Stream.AArch64.absorb_framed } (Proof.CmacTripleDes.AArch64.Scrub.absorbOk 688)),
  Spec.Cmac.tdesFinishApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.finish
    verified := Proof.CmacTripleDes.Stream.AArch64.finish_framed } (Proof.CmacTripleDes.AArch64.Scrub.finishOk 640))]

end VG.Artifacts.CmacTripleDes.AArch64
