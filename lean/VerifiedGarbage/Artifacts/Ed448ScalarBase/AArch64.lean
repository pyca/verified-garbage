import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 base-point multiplication on AArch64

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

namespace VG.Artifacts.Ed448ScalarBase.AArch64

def artifacts : List Artifact := [
  { Spec.Ed448.scalarBaseApi with
    target := AArch64.target
    doc := Spec.Ed448.scalarBaseApi.doc (notes := ["Uses baseline integer instructions. \
      Expands the scalar's 456 bits into bytes, then for each bit from the top doubles `R` and \
      adds the base point to it with RFC 8032's projective formulas, and swaps the sum into `R` \
      with a mask of the bit: the same operations for every bit. Field elements are eight 56-bit \
      limbs; a product accumulates two-word coefficients by columns (a square computes each \
      cross product once) and reduces them with `2^448 = 2^224 + 1` (mod p), and sums and \
      differences are reduced to limbs of 56 bits. `Z` is inverted with X448's addition chain \
      for `p - 2`. The function saves `x19` and `x20` in the first 16 bytes of \
      `scratch`."])
    code := Impl.Ed448.AArch64.scalarBase
    contract := Spec.Ed448.scalarBaseContract AArch64.abi
    verified := Proof.Ed448.AArch64.scalarBase_verified Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448ScalarBase.AArch64
