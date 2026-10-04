import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Frame

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64

The functions call nothing: the return address stays in `x30`. They keep
their working space in a frame of their own on the stack
(`Proof/CmacTripleDes/AArch64/Frame.lean`).
-/

namespace VG.Artifacts.CmacTripleDes.AArch64

open VG.Proof.CmacTripleDes.AArch64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation looks up DES's S-boxes with AdvSIMD `tbl` in tables held in the vector \
  registers (two boxes to a 64-byte table), which takes a time independent of the index, and \
  computes its bit permutations as rotations and masks; the halves are kept rotated and spread \
  so that the expansion is a byte layout, and the round keys are spread once per call (before all the blocks of an update)."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x3 Impl.CmacTripleDes.AArch64.init
    contract := Spec.Cmac.tdesInitContract AArch64.abi 640
    stack := 640
    verified := init_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesUpdateApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x4 Impl.CmacTripleDes.AArch64.update
    contract := Spec.Cmac.tdesUpdateContract AArch64.abi 640
    stack := 640
    verified := update_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesFinalizeApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x4 Impl.CmacTripleDes.AArch64.finalize
    contract := Spec.Cmac.tdesFinalizeContract AArch64.abi 640
    stack := 640
    verified := finalize_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CmacTripleDes.AArch64
