module
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract

import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.CT

/-! # Shared Miller–Rabin callable verified against its merged contract -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem round_verified (M : Mont) :
    Verified target (VG.Impl.MillerRabin.AArch64.round M.mm)
      (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact) :=
  Verified.of_correct (round_correct M) (round_ct M) round_implies

end VG.Proof.MillerRabin.AArch64
