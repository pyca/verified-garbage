module
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.MillerRabin.Contract

import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Verified shared round with a generic inlined Montgomery backend -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

theorem round_verified (M : Mont)
    (hload : ∀ i ∈ instrs (round M.mm), loadsMxcsr i = false) :
    Verified target (round M.mm) (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.extended 120) :=
  Verified.of_correct (round_correct M hload) (round_ct M) round_implies

end VG.Proof.MillerRabin.X86_64
