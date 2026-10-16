module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import Mathlib.Tactic.Finiteness.Attr

/-!
# The baseline shared round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.AArch64.Base.variant`
(`Variants/MillerRabin/AArch64/Base.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.AArch64.Base

open VG.Proof.MillerRabin.AArch64 VG.Proof.Bignum.AArch64

def variant : RoundImpl where
  mont := Mont.base
  noFrames := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.AArch64.Base
