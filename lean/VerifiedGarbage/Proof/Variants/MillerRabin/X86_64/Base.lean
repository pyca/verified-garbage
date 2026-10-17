module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
public import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-!
# The baseline shared Miller–Rabin round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.X86_64.Base.variant`
(`Variants/MillerRabin/X86_64/Base.lean`), with the proofs its interface asks
for. Its callers inline the compact `vg_rsa_mont_mul` loop: by calls, DSA's
signing and verification were 2–5% slower on AMD Zen 3.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86_64.Base

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl where
  mont := Mont.fnBase
  mm := Mont.fnBase.mm
  mmOk := inline_call_inlineOk (by decide +kernel)
  mmInline := inline_call_inline (by decide +kernel)
  mxSafe := by decide +kernel
  spSafe := by decide +kernel
  depth := by decide +kernel
  arithDepth := by intro o a b; rfl
  arithSafe := by intro o a b; rfl
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.X86_64.Base
