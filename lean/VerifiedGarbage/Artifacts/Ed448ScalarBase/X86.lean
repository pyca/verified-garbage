import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed448.X86.BaseVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 base-point multiplication on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

namespace VG.Artifacts.Ed448ScalarBase.X86

def artifacts : List Artifact := [
  { Spec.Ed448.scalarBaseApi with
    target := X86.target
    doc := Spec.Ed448.scalarBaseApi.doc (notes := ["Expands the scalar's 456 bits into \
      bytes, then for each bit from the top doubles `R` and adds the base point to it with \
      RFC 8032's projective formulas, and swaps the sum into `R` with a mask of the bit: the \
      same operations for every bit. Field elements are X448's twenty-eight 16-bit limbs in \
      `scratch`, and the field arithmetic is by calls of `vg_gf448_r16_mul`, \
      `vg_gf448_r16_add` and `vg_gf448_r16_sub`; `Z` is inverted with X448's addition chain \
      for `p - 2`. Callee-saved registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.Ed448.X86.scalarBase
    contract := Spec.Ed448.scalarBaseContract X86.abi 20
    stack := 20
    verified := Proof.Ed448.X86.scalarBase_verified Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448ScalarBase.X86
