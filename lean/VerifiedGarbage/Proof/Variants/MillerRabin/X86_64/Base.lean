module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase

/-!
# The baseline shared Miller–Rabin round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.X86_64.Base.variant`
(`Variants/MillerRabin/X86_64/Base.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86_64.Base

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl where
  mont := Mont.fnBase
  mxSafe := by decide +kernel
  spSafe := by decide +kernel
  depth := by decide +kernel
  arithSafe := by intro o a b; rfl
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.X86_64.Base
