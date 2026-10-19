module

public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubCode

/-!
# Precomputed RSA public operation: with AVX512_IFMA: the variant's code and proofs

The variant `VG.Variants.RsaPublicPrecomputed.X86_64.Ifma.variant`
(`Variants/RsaPublicPrecomputed/X86_64/Ifma.lean`), with the proofs its
interface asks for: for `e = 65537` and 2048-, 3072- and 4096-bit moduli,
the vector code; otherwise the ADX code's.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ "_ifma"
  code := Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm
  ok := Ifma.Pub.checked_correct _ (by decide +kernel)
  ct := Ifma.Pub.checked_ct _ FoldedPublic.adx_final_ct
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]

end VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma
