module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified

/-! # Shared round implementations for generic callers -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Impl.MillerRabin.AArch64

structure RoundImpl where
  mont : Mont
  noFrames : (round mont.mm).noFrames = true
  /-- Its Montgomery multiplication has no frames, so a caller of it that is
  called itself uses no stack (e.g. `vg_ffdh_parameter_candidate`). -/
  mmNoFrames : ∀ o a b, (mont.mm o a b).noFrames = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).name ++ v.suffix

def RoundImpl.code (v : RoundImpl) : Prog isa := round v.mont.mm

def RoundImpl.kernel (v : RoundImpl) : Kernel := Kernel.called v.mont v.name v.noFrames

theorem RoundImpl.verified (v : RoundImpl) : Verified target v.code
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact) := by
  exact round_verified v.mont

end VG.Proof.MillerRabin.AArch64
