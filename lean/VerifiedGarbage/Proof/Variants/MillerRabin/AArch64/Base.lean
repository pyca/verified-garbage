module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SplitIfs

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
  mmNoFrames := by
    intro o a b
    show (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b).noFrames = true
    simp only [VG.Impl.Bignum.AArch64.SquareEightCall.mm, VG.Impl.Bignum.AArch64.SquareCall.mm,
      VG.Impl.Bignum.AArch64.SquareCall.call, VG.Impl.Bignum.AArch64.BlockedRedc.mm,
      VG.Impl.Bignum.AArch64.Square.montMul]
    split_ifs with h1 <;> first
      | rfl
      | (obtain ⟨rfl, rfl, rfl⟩ := h1; decide +kernel)
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.AArch64.Base
