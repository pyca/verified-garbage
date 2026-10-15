module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
public import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.Framework.X86_64.Call
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Verified shared round with a generic inlined Montgomery backend -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

theorem round_verified (M : Mont)
    (hload : ∀ i ∈ instrs (round M.mm), loadsMxcsr i = false) :
    Verified target (round M.mm) (Spec.MillerRabin.roundContract abi Spec.MillerRabin.extended 120) :=
  Verified.of_correct (round_correct M hload) (round_ct M) round_implies

end VG.Proof.MillerRabin.X86_64
