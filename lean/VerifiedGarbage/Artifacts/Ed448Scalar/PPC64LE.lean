module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 scalar arithmetic on PPC64LE

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. The function reduces all 912 input bits from \
      the top, one at a time, in fourteen 32-bit limbs: the remainder doubled with the bit as the \
      carry in, then `L` subtracted (as an addition of `2^448 - L`, whose carry out says whether \
      the remainder was at least `L`) and selected with a mask. The nonvolatile registers it uses \
      are saved at bytes 1064 to 1159 of `scratch`."]
    code := Impl.Ed448.PPC64LE.scalarReduce
    verified := Proof.Ed448.PPC64LE.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. The function reduces `k`, `s` and `r` modulo \
      `L` as `vg_ed448_scalar_reduce` does, computes the 896-bit product of the first two row by \
      row with `mulld` (X448's PPC64LE product, without its reduction), adds the third, and \
      reduces the sum the same way. The nonvolatile registers it uses are saved at bytes 1064 to \
      1159 of `scratch`."]
    code := Impl.Ed448.PPC64LE.scalarMulAdd
    verified := Proof.Ed448.PPC64LE.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.PPC64LE
