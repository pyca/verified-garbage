module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase

/-! # The baseline shared Miller–Rabin round -/

@[expose] public section

namespace VG.Variants.MillerRabin.X86_64.Base

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl where
  mont := Mont.fnBase
  mxSafe := by decide +kernel
  spSafe := by decide +kernel
  depth := by decide +kernel
  arithSafe := by intro o a b; rfl
  suffix := ""
  features := []

end VG.Variants.MillerRabin.X86_64.Base
