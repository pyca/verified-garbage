module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend

/-! # Baseline x86-64 Montgomery arithmetic for DSA

Inline: by calls of `vg_rsa_mont_mul`, signing and verification were 2–5%
slower on AMD Zen 3. -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Base
open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64

def variant : Backend where
  mm := Mont.base.mm
  mont := Mont.base
  note := "inline Montgomery multiplication"
  suffix := ""
  features := []
  signIn := by decide +kernel
  verifyIn := by decide +kernel
  signEq := Code.inline_of_noCalls (by decide +kernel)
  verifyEq := Code.inline_of_noCalls (by decide +kernel)
  signMx := by decide +kernel
  verifyMx := by decide +kernel
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)

end VG.Variants.DsaArithmetic.X86_64.Base
