module

public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Frame
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64

The functions call nothing: the return address stays in `x30`. They keep
their working space in a frame of their own on the stack
(`Proof/CmacTripleDes/AArch64/Frame.lean`).
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.AArch64

open VG.Proof.CmacTripleDes.AArch64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation looks up DES's S-boxes with AdvSIMD `tbl` in tables held in the vector \
  registers (two boxes to a 64-byte table), which takes a time independent of the index, and \
  computes its bit permutations as rotations and masks; the halves are kept rotated and spread \
  so that the expansion is a byte layout, and the round keys are spread once per call (before all the blocks of an update)."

def artifacts : List Artifact := [
  Spec.Cmac.tdesInitApi.artifact AArch64.target {
    notes := [desNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.AArch64.init
    stack := 640
    verified := init_framed },
  Spec.Cmac.tdesUpdateApi.artifact AArch64.target {
    notes := [desNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x4 Impl.CmacTripleDes.AArch64.update
    stack := 640
    verified := update_framed },
  Spec.Cmac.tdesFinalizeApi.artifact AArch64.target {
    notes := [desNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x4 Impl.CmacTripleDes.AArch64.finalize
    stack := 640
    verified := finalize_framed },
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target {
    notes := [desNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.streamInit
    stack := 640
    verified := Proof.CmacTripleDes.Stream.AArch64.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target {
    notes := [desNote]
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x4 Impl.CmacTripleDes.Stream.AArch64.absorb
    stack := 688
    verified := Proof.CmacTripleDes.Stream.AArch64.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact AArch64.target {
    notes := [desNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.finish
    stack := 640
    verified := Proof.CmacTripleDes.Stream.AArch64.finish_framed }]

end VG.Artifacts.CmacTripleDes.AArch64
