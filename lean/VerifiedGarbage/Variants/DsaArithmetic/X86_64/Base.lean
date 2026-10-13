module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend

/-! # Baseline x86-64 Montgomery arithmetic for DSA -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Base
open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64

def variant : Backend where
  mul := Mont.base.mm
  suffix := ""
  features := []
  signVerified := signing_verified Mont.base (by decide +kernel)
  verifyVerified := verifying_verified Mont.base (by decide +kernel)
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)

end VG.Variants.DsaArithmetic.X86_64.Base
