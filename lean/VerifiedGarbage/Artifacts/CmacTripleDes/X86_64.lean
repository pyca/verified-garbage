import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Frame

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64

The functions call nothing. They keep their working space in a frame of
their own on the stack (`Proof/CmacTripleDes/X86_64/Frame.lean`).
-/

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across a 64-bit word, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := X86_64.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.X86_64.init
    contract := Spec.Cmac.tdesInitContract X86_64.abi 648
    stack := 648
    verified := init_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesUpdateApi with
    target := X86_64.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r8 Impl.CmacTripleDes.X86_64.update
    contract := Spec.Cmac.tdesUpdateContract X86_64.abi 648
    stack := 648
    verified := update_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesFinalizeApi with
    target := X86_64.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r8 Impl.CmacTripleDes.X86_64.finalize
    contract := Spec.Cmac.tdesFinalizeContract X86_64.abi 648
    stack := 648
    verified := finalize_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CmacTripleDes.X86_64
