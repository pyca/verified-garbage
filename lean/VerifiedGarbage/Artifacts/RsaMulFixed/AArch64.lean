module

public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedHelper
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Fixed-index RSA Montgomery products on AArch64

The products DSA repeats (`MulFixedCall.shared`), each shared by one
helper that runs the eight-limb product. -/

@[expose] public section

namespace VG.Artifacts.RsaMulFixed.AArch64
open VG.AArch64

def helper (ix : Spec.Rsa.MontMulFixed.Indices)
    (v : Verified target (Proof.Bignum.AArch64.Mont.productEight.mm ix.o ix.a ix.b)
      (Spec.Rsa.MontMulFixed.mulContract ix abi)) : Artifact :=
  (Spec.Rsa.MontMulFixed.mulApi ix).artifact target {
    notes := ["Baseline AArch64: the eight-limb product kernel with blocked reduction when the \
        width is a multiple of eight limbs; other widths retain the row-wise multiplication."]
    code := Proof.Bignum.AArch64.Mont.productEight.mm ix.o ix.a ix.b
    verified := v }

open Proof.Bignum.AArch64 in
def artifacts : List Artifact := [
  helper ⟨5, 1, 4⟩ (MulFixedHelper.verified Mont.productEight ⟨5, 1, 4⟩),
  helper ⟨6, 5, 6⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 5, 6⟩),
  helper ⟨6, 4, 7⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 4, 7⟩),
  helper ⟨5, 5, 4⟩ (MulFixedHelper.verified Mont.productEight ⟨5, 5, 4⟩),
  helper ⟨6, 6, 5⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 6, 5⟩),
  helper ⟨6, 6, 7⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 6, 7⟩),
  helper ⟨1, 1, 4⟩ (MulFixedHelper.verified Mont.productEight ⟨1, 1, 4⟩),
  helper ⟨6, 5, 1⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 5, 1⟩)]

end VG.Artifacts.RsaMulFixed.AArch64
