module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.AArch64.Base
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont

/-! # DSA with the shared AArch64 Montgomery arithmetic backend

RSA's Montgomery multiplication with eight-limb products
(`Mont.productEight`, as RSA's CRT window and `vg_rsa_mont_mul` use, the
repeated ones by calls of fixed-index helpers, `Mont.calledProductEight`):
products of distinct operands use the scheduled eight-limb kernel when the
width is a multiple of eight words (every DSA p), and in-place squares RSA's
scheduled squaring kernel. -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.AArch64.Base

open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

def variant : Backend := Proof.Variants.DsaArithmetic.AArch64.Base.variant

end VG.Variants.DsaArithmetic.AArch64.Base
