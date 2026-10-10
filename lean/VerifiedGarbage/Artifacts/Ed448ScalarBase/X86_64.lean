import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 base-point multiplication on x86-64

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

namespace VG.Artifacts.Ed448ScalarBase.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.scalarBaseApi with
    target := X86_64.target
    doc := Spec.Ed448.scalarBaseApi.doc (notes := ["Expands the scalar's 456 bits into \
      bytes, then for each bit from the top doubles `R` and adds the base point to it with \
      RFC 8032's projective formulas, by calls of `vg_ed448_r64_point_double` and \
      `vg_ed448_r64_point_add_affine` (the base point has `Z = 1`), and swaps the sum into `R` \
      with a mask of the bit: the same operations for every bit. Field elements are X448's seven 64-bit words, multiplied \
      with `mul` by columns; `Z` is inverted with X448's addition chain for `p - 2`, its part \
      shared with the square root by a call of `vg_gf448_r64_pow223`. \
      Callee-saved registers are saved in the first 48 bytes of `scratch`, and the output's \
      address in the next 8."])
    code := Impl.Ed448.X86_64.scalarBase
    contract := Spec.Ed448.scalarBaseContract X86_64.abi 8
    stack := 8
    verified := Proof.Ed448.X86_64.scalarBase_verified Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448ScalarBase.X86_64
