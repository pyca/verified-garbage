import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X448.X86
import VerifiedGarbage.Proof.X448.X86.FnVerified

/-! # Arithmetic in curve448's field, in radix `2^16`, on x86 (32-bit) -/

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
  { mulApi with
    target := X86.target
    doc := mulApi.doc (notes := notes)
    code := mulFn
    contract := mulContract X86.abi
    verified := mulFn_verified
    ofSig := by unfold mulContract binContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { addApi with
    target := X86.target
    doc := addApi.doc (notes := notes)
    code := addFn
    contract := addContract X86.abi
    verified := addFn_verified
    ofSig := by unfold addContract binContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { subApi with
    target := X86.target
    doc := subApi.doc (notes := notes)
    code := subFn
    contract := subContract X86.abi
    verified := subFn_verified
    ofSig := by unfold subContract binContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { mulA24Api with
    target := X86.target
    doc := mulA24Api.doc (notes := notes)
    code := mulA24Fn
    contract := mulA24Contract X86.abi
    verified := mulA24Fn_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Gf448R16.X86
