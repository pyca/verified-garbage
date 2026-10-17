module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Implementations of the shared Miller–Rabin round on ARMv7, for generic callers

A `RoundImpl` is verified against the contract its callers use
(`roundContract`, `Proof/MillerRabin/Arm/Contract.lean`), within the 56
bytes of stack its callers leave it, which gives the shared contract
(`RoundImpl.verifiedSpec`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm

open VG VG.Arm

structure RoundImpl where
  code : Prog isa
  verified : Verified target code roundContract
  stack : FrameStack.armStack code ≤ 56
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).name ++ v.suffix

theorem RoundImpl.verifiedSpec (v : RoundImpl) : Verified target v.code
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56) :=
  v.verified.of_implies round_implies

end VG.Proof.MillerRabin.Arm
