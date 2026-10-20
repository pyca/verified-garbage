module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86.Update

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions call nothing. They keep their working space in a frame of
their own on the stack, with a copy of their stack arguments
(`Proof/CmacTripleDes/Stream/X86/Frame.lean`): they save our caller's
registers in the working space (or, `stream_init`'s `ebx`, in the state),
and reload their stack arguments.
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86

open VG.Proof.CmacTripleDes.X86

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
  Spec.Cmac.tdesStreamInitApi.artifact X86.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.X86.withStackScratch 660 3 Impl.CmacTripleDes.Stream.X86.streamInit
    stack := 680
    verified := Proof.CmacTripleDes.Stream.X86.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact X86.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.X86.withStackScratch 716 5 Impl.CmacTripleDes.Stream.X86.absorb
    stack := 740
    verified := Proof.CmacTripleDes.Stream.X86.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact X86.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.X86.withStackScratch 712 4 Impl.CmacTripleDes.Stream.X86.finish
    stack := 736
    verified := Proof.CmacTripleDes.Stream.X86.finish_framed }]

end VG.Artifacts.CmacTripleDes.X86
