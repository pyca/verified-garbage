module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import Mathlib.Tactic.Finiteness.Attr

/-! # The baseline shared round -/

@[expose] public section

namespace VG.Variants.MillerRabin.AArch64.Base

open VG.Proof.MillerRabin.AArch64 VG.Proof.Bignum.AArch64

def variant : RoundImpl where
  mont := Mont.base
  noFrames := by decide +kernel
  suffix := ""
  features := []

end VG.Variants.MillerRabin.AArch64.Base
