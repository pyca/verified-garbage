module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified

/-! # Shared round implementations for generic callers -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Impl.MillerRabin.AArch64

structure RoundImpl where
  /-- The Montgomery multiplication of the callers' own arithmetic, which
  they inline. -/
  mont : Mont
  /-- The Montgomery multiplication of the shared round, which its callers
  reach by a call: a faster one costs code once, not at every caller. -/
  roundMont : Mont
  noFrames : (round roundMont.mm).noFrames = true
  /-- Its Montgomery multiplication has no frames, so a caller of it that is
  called itself uses no stack (e.g. `vg_ffdh_parameter_candidate`). -/
  mmNoFrames : ∀ o a b, (mont.mm o a b).noFrames = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

def RoundImpl.code (v : RoundImpl) : Prog isa := round v.roundMont.mm

def RoundImpl.kernel (v : RoundImpl) : Kernel := Kernel.called v.roundMont v.name v.noFrames

theorem RoundImpl.verified (v : RoundImpl) : Verified target v.code
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact) := by
  exact round_verified v.roundMont

end VG.Proof.MillerRabin.AArch64
