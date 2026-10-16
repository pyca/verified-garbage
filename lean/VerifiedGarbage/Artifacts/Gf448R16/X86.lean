module

public import VerifiedGarbage.Proof.X448.X86.FnVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X448.X86.FnLit

/-! # Arithmetic in curve448's field, in radix `2^16`, on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Gf448R16.X86

open VG.Spec.X448.Field16 VG.Impl.X448.X86 VG.Proof.X448.X86

/-- How the functions work. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `ebx`, `esi`, \
  `edi` and `ebp` in its own working space and reads the operands and writes the result through \
  pointers. A product's 28 rows of 32-bit `mul`s propagate their carries as they go; the 56 \
  limbs of the product are folded with `2^448 = 2^224 + 1`; sums, differences (with twice the \
  prime added) and products are normalized by carrying, folding the carry out of the top limb \
  into limbs 0 and 14, twice, and carrying again."]

def artifacts : List Artifact := [
  mulApi.artifact X86.target {
    notes := notes
    code := mulFn
    verified := mulFn_verified },
  addApi.artifact X86.target {
    notes := notes
    code := addFn
    verified := addFn_verified },
  subApi.artifact X86.target {
    notes := notes
    code := subFn
    verified := subFn_verified },
  mulA24Api.artifact X86.target {
    notes := notes
    code := mulA24Fn
    verified := mulA24Fn_verified }]

end VG.Artifacts.Gf448R16.X86
