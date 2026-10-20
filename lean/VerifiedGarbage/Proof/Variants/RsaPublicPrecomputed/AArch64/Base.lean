module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
public import VerifiedGarbage.Proof.Rsa.AArch64.PublicImpl
public import VerifiedGarbage.Proof.Rsa.AArch64.FoldedChecked

/-!
# Precomputed RSA public operation on AArch64: Base: the variant's code and proofs

The variant `VG.Variants.RsaPublicPrecomputed.AArch64.Base.variant`
(`Variants/RsaPublicPrecomputed/AArch64/Base.lean`), with the proofs its
interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPublicPrecomputed.AArch64.Base

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ ""
  code := Impl.Rsa.AArch64.Folded.checked Mont.productEight.mm
  ok := FoldedPublic.checked_correct _
  ct := FoldedPublic.checked_constantTime _
  keepsV := by decide +kernel
  spSafe := Code.all_of_forall (fun _ => rfl) _
  depth := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.RsaPublicPrecomputed.AArch64.Base
