module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.CmacTripleDes.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

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
their own on the stack (`Proof/CmacTripleDes/Arm/Frame.lean`): they save our
caller's registers in the working space, and the return address stays in
`lr`.
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.Arm

open VG.Proof.CmacTripleDes.Arm

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across 32-bit words, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  Spec.Cmac.tdesInitApi.artifact Arm.target {
    notes := [desNote]
    code := Impl.StackScratch.Arm.withRegScratch 640 .r3 Impl.CmacTripleDes.Arm.init
    stack := 640
    verified := init_framed },
  Spec.Cmac.tdesUpdateApi.artifact Arm.target {
    notes := [desNote]
    code := Impl.StackScratch.Arm.withStackScratch 648 0 Impl.CmacTripleDes.Arm.update
    stack := 648
    verified := update_framed },
  Spec.Cmac.tdesFinalizeApi.artifact Arm.target {
    notes := [desNote]
    code := Impl.StackScratch.Arm.withStackScratch 648 0 Impl.CmacTripleDes.Arm.finalize
    stack := 648
    verified := finalize_framed }]

end VG.Artifacts.CmacTripleDes.Arm
