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

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation looks up DES's S-boxes with AdvSIMD `tbl` in tables held in the vector \
  registers (two boxes to a 64-byte table), which takes a time independent of the index, and \
  computes its bit permutations as rotations and masks; the halves are kept rotated and spread \
  so that the expansion is a byte layout, and the round keys are spread once per call (before all the blocks of an update)."

/-- How the streaming functions are built. -/
def streamNote : String :=
  "This implementation's streaming functions are built from three pieces of code, run inline on \
  the streaming state: one expands the key and derives the subkeys, one chains whole blocks, and \
  one masks, pads and encrypts the last block."

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.streamInit
    stack := 640
    verified := Proof.CmacTripleDes.Stream.AArch64.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x4 Impl.CmacTripleDes.Stream.AArch64.absorb
    stack := 688
    verified := Proof.CmacTripleDes.Stream.AArch64.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact AArch64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.Stream.AArch64.finish
    stack := 640
    verified := Proof.CmacTripleDes.Stream.AArch64.finish_framed }]

end VG.Artifacts.CmacTripleDes.AArch64
