module

public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64

The functions call nothing. They keep their working space in a frame of
their own on the stack (`Proof/CmacTripleDes/X86_64/Frame.lean`).
-/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across a 64-bit word, as a tree of multiplexers \
  over constants."

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
    verified := finalize_framed }]

end VG.Artifacts.CmacTripleDes.X86_64
