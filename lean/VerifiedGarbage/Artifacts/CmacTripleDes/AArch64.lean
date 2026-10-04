import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Verified

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64

The functions call nothing and use no stack: the return address stays in `x30`.
-/

namespace VG.Artifacts.CmacTripleDes.AArch64

open VG.Proof.CmacTripleDes.AArch64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation looks up DES's S-boxes with AdvSIMD `tbl` in tables held in the vector \
  registers (two boxes to a 64-byte table), which takes a time independent of the index, and \
  computes its bit permutations as rotations and masks; the halves are kept rotated and spread \
  so that the expansion is a byte layout, and the round keys are spread once per block."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.AArch64.init
    contract := Spec.Cmac.tdesInitContract AArch64.abi 0
    verified := init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesUpdateApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.AArch64.update
    contract := Spec.Cmac.tdesUpdateContract AArch64.abi 0
    verified := update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesFinalizeApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.AArch64.finalize
    contract := Spec.Cmac.tdesFinalizeContract AArch64.abi 0
    verified := finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CmacTripleDes.AArch64
