module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Adx

/-! # BMI2/ADX Montgomery arithmetic for DSA

Reuse RSA's shared `vg_rsa_mont_mul_adx` kernel, including tiled products
and triangular squaring for aligned widths. Calls avoid duplicating those
kernels at each arithmetic site; their return address uses eight stack bytes.
The secret-exponent windows square by `vg_rsa_lazy_mont_mul_adx`.
-/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Adx

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend := Proof.Variants.DsaArithmetic.X86_64.Adx.variant

end VG.Variants.DsaArithmetic.X86_64.Adx
