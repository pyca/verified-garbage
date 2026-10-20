module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions call nothing. They keep their working space in a frame of
their own on the stack (`Proof/CmacTripleDes/Stream/Arm/Frame.lean`): they
save our caller's registers in the working space, and the return address
stays in `lr`.
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.Arm

open VG.Proof.CmacTripleDes.Arm

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across 32-bit words, as a tree of multiplexers \
  over constants."

/-- How the streaming functions are built. -/
def streamNote : String :=
  "This implementation's streaming functions are built from three pieces of code, run inline on \
  the streaming state: one expands the key and derives the subkeys, one chains whole blocks, and \
  one masks, pads and encrypts the last block."

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact Arm.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.Arm.withRegScratch 640 .r3 Impl.CmacTripleDes.Stream.Arm.streamInit
    stack := 640
    verified := Proof.CmacTripleDes.Stream.Arm.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact Arm.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.Arm.withStackScratch 704 2 Impl.CmacTripleDes.Stream.Arm.absorb
    stack := 708
    verified := Proof.CmacTripleDes.Stream.Arm.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact Arm.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.Arm.withStackScratch 656 1 Impl.CmacTripleDes.Stream.Arm.finish
    stack := 660
    verified := Proof.CmacTripleDes.Stream.Arm.finish_framed }]

end VG.Artifacts.CmacTripleDes.Arm
