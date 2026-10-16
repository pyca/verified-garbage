module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic, its stack allowance and proofs of
both complete callers. This admits both inline arithmetic and calls to a
shared kernel. The generic registration emits both callers for every backend.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

structure Backend where
  mul : Nat → Nat → Nat → Prog isa
  stack : Nat := 0
  suffix : String
  features : List String
  signVerified : Verified target (SignVerify.sign mul) (Spec.Dsa.signContract abi stack)
  verifyVerified : Verified target (SignVerify.verify mul) (Spec.Dsa.verifyContract abi stack)
  signSp : (SignVerify.sign mul).all (fun i => !isa.writesSp i) = true
  signDepth : 16 * (SignVerify.sign mul).aarch64Depth ≤ stack
  stackBound : stack < 2 ^ 32
  verifySp : (SignVerify.verify mul).all (fun i => !isa.writesSp i) = true

end VG.Proof.Dsa.AArch64
