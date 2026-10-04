import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.CmacTripleDes.X86.Frame

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
(`Proof/CmacTripleDes/X86/Frame.lean`): they save our caller's registers in
the working space, and reload their stack arguments.
-/

namespace VG.Artifacts.CmacTripleDes.X86

open VG.Proof.CmacTripleDes.X86

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across 32-bit words, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := X86.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.StackScratch.X86.withStackScratch 660 3 Impl.CmacTripleDes.X86.init
    contract := Spec.Cmac.tdesInitContract X86.abi 660
    stack := 660
    verified := init_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesUpdateApi with
    target := X86.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.StackScratch.X86.withStackScratch 664 4 Impl.CmacTripleDes.X86.update
    contract := Spec.Cmac.tdesUpdateContract X86.abi 664
    stack := 664
    verified := update_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesFinalizeApi with
    target := X86.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.StackScratch.X86.withStackScratch 664 4 Impl.CmacTripleDes.X86.finalize
    contract := Spec.Cmac.tdesFinalizeContract X86.abi 664
    stack := 664
    verified := finalize_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CmacTripleDes.X86
