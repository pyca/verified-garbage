module

public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Frame
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64

The functions call nothing. They keep their working space in a frame of
their own on the stack (`Proof/CmacTripleDes/X86_64/Frame.lean`,
`Proof/CmacTripleDes/Stream/X86_64/Frame.lean`).
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
  "This implementation runs the code of `vg_cmac_triple_des_init`, `vg_cmac_triple_des_update` or \
  `vg_cmac_triple_des_finalize` inline, on the streaming state."

def artifacts : List Artifact := [
  Spec.Cmac.tdesInitApi.artifact X86_64.target {
    notes := [desNote]
    code := Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.X86_64.init
    stack := 648
    verified := init_framed },
  Spec.Cmac.tdesUpdateApi.artifact X86_64.target {
    notes := [desNote]
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r8 Impl.CmacTripleDes.X86_64.update
    stack := 648
    verified := update_framed },
  Spec.Cmac.tdesFinalizeApi.artifact X86_64.target {
    notes := [desNote]
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r8 Impl.CmacTripleDes.X86_64.finalize
    stack := 648
    verified := finalize_framed },
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
