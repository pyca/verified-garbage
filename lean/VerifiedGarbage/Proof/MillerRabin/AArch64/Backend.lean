module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide

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
  /-- Neither touches PSTATE.DIT. -/
  noDit : (round roundMont.mm).all (fun i => !i.touchesDit) = true
  mmNoDit : ∀ o a b, (mont.mm o a b).all (fun i => !i.touchesDit) = true
  /-- Neither writes PSTATE.DIT nor calls anything indirectly: what a caller
  whose cleanup is part of its code states of the code it runs
  (`Scrub.verifiedScrubbedOf`). -/
  side : Scrub.sideAll (fun i => !i.writesDit) (round roundMont.mm) = true
  mmSide : ∀ o a b, Scrub.sideAll (fun i => !i.writesDit) (mont.mm o a b) = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

def RoundImpl.kernel (v : RoundImpl) : Kernel := Kernel.called v.roundMont v.name v.noFrames

end VG.Proof.MillerRabin.AArch64
