module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Shared round implementations for generic callers -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Impl.MillerRabin.AArch64

structure RoundImpl where
  mont : Mont
  noFrames : (round mont.mm).noFrames = true
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
