module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked

/-!
# Precomputed RSA public operation: Base: the variant's code and proofs

The variant `VG.Variants.RsaPublicPrecomputed.X86_64.Base.variant`
(`Variants/RsaPublicPrecomputed/X86_64/Base.lean`), with the proofs its
interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Base

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl where
  name := "vg_rsa_public_precomputed_checked"
  code := Impl.Rsa.X86_64.Folded.checked Mont.base.mm
  ok := FoldedPublic.checked_correct _ (by decide +kernel)
  ct := FoldedPublic.checked_ct _ FoldedPublic.base_final_ct
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_spTest (by decide +kernel)
  level := .sse
  side := by lit_decide
  up := fun _ => by rw [X86_64.Scrub.upCallee, ← X86_64.Scrub.upF_eq]; lit_decide
  suffix := ""
  features := []

end VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Base
