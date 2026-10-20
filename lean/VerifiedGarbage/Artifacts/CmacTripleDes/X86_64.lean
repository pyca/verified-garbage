module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64

The functions call nothing. They keep their working space in a frame of
their own on the stack (`Proof/CmacTripleDes/Stream/X86_64/Frame.lean`).
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across a 64-bit word, as a tree of multiplexers \
  over constants."


/-- How the streaming functions are built. -/
def streamNote : String :=
  "This implementation's streaming functions are built from three pieces of code, run inline on \
  the streaming state: one expands the key and derives the subkeys, one chains whole blocks, and \
  one masks, pads and encrypts the last block."

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact X86_64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.Stream.X86_64.streamInit
    stack := 648
    verified := Proof.CmacTripleDes.Stream.X86_64.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact X86_64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.X86_64.withStackScratch 696 .r8 Impl.CmacTripleDes.Stream.X86_64.absorb
    stack := 696
    verified := Proof.CmacTripleDes.Stream.X86_64.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact X86_64.target {
    notes := [desNote, streamNote]
    code := Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.Stream.X86_64.finish
    stack := 648
    verified := Proof.CmacTripleDes.Stream.X86_64.finish_framed }]

end VG.Artifacts.CmacTripleDes.X86_64
