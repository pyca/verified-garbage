module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.CT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Shared Miller–Rabin callable verified against its merged contract -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem round_verified (M : Mont) :
    Verified target (VG.Impl.MillerRabin.AArch64.round M.mm)
      (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact) :=
  Verified.of_correct (round_correct M) (round_ct M) round_implies

end VG.Proof.MillerRabin.AArch64
