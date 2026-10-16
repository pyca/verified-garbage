module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Base

/-! # Baseline x86-64 Montgomery arithmetic for DSA

Reuse RSA's shared Montgomery kernel to avoid duplicating it at each
arithmetic site, including the squarings in R² setup. The secret-exponent
windows square by `vg_rsa_lazy_mont_mul`.
-/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Base

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend := Proof.Variants.DsaArithmetic.X86_64.Base.variant

end VG.Variants.DsaArithmetic.X86_64.Base
