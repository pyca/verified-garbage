module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Shared round implementations for generic RSA and FFDH callers -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

structure RoundImpl where
  mont : Mont
  mxSafe : (round mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : (round mont.mm).all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  (Spec.MillerRabin.roundApi Spec.MillerRabin.extended).name ++ v.suffix

def RoundImpl.code (v : RoundImpl) : Prog isa := round v.mont.mm

theorem RoundImpl.verified (v : RoundImpl) : Verified target v.code
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.extended 120) := by
  apply round_verified v.mont
  have h := v.mxSafe
  rw [Code.allInstrs_eq] at h
  intro i hi
  have := List.all_eq_true.mp h i hi
  simpa only [Bool.not_eq_true'] using this

end VG.Proof.MillerRabin.X86_64
