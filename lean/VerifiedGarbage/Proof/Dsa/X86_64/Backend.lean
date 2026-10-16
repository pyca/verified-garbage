module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic, its stack allowance and proofs of
both complete callers. This admits both inline arithmetic and calls to a
shared kernel. The generic registration emits both callers for every backend.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Proof.Bignum.X86_64

structure Backend where
  sq : Prog isa
  mul : Nat → Nat → Nat → Prog isa
  stack : Nat := 0
  suffix : String
  features : List String
  signVerified : Verified target (SignVerify.sign sq mul) (Spec.Dsa.signContract abi stack)
  verifyVerified : Verified target (SignVerify.verify sq mul) (Spec.Dsa.verifyContract abi stack)
  signSp : (SignVerify.sign sq mul).all (fun i => !isa.writesSp i) = true
  verifySp : (SignVerify.verify sq mul).all (fun i => !isa.writesSp i) = true
  signDepth : (SignVerify.sign sq mul).x86_64Depth ≤ stack
  stackBound : stack < 2 ^ 32

end VG.Proof.Dsa.X86_64
