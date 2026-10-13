module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic, its stack allowance and proofs of
both complete callers. This admits both inline arithmetic and calls to a
shared kernel. The generic registration emits both callers for every backend.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Proof.Bignum.X86_64

structure Backend where
  mul : Nat → Nat → Nat → Prog isa
  stack : Nat := 0
  suffix : String
  features : List String
  signVerified : Verified target (SignVerify.sign mul) (Spec.Dsa.signContract abi stack)
  verifyVerified : Verified target (SignVerify.verify mul) (Spec.Dsa.verifyContract abi stack)
  signSp : (SignVerify.sign mul).all (fun i => !isa.writesSp i) = true
  verifySp : (SignVerify.verify mul).all (fun i => !isa.writesSp i) = true

end VG.Proof.Dsa.X86_64
