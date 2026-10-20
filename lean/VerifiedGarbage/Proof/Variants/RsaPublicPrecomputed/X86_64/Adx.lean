module

public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedChecked

/-!
# Precomputed RSA public operation: Adx: the variant's code and proofs

The variant `VG.Variants.RsaPublicPrecomputed.X86_64.Adx.variant`
(`Variants/RsaPublicPrecomputed/X86_64/Adx.lean`), with the proofs its
interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ "_adx"
  code := Impl.Rsa.X86_64.Folded.checked Mont.adxSquare.mm
  ok := FoldedPublic.checked_correct _ (by decide +kernel)
  ct := FoldedPublic.checked_ct _ FoldedPublic.adx_final_ct
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_adx"
  features := ["bmi2", "adx"]

end VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Adx
