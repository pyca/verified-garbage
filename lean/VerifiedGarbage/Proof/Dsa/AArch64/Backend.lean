module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Arithmetic variants for the complete DSA entry points on AArch64

A backend supplies Montgomery arithmetic and proofs of both complete
callers, as on x86-64 (`Proof/Dsa/X86_64/Backend.lean`). The generic
registration emits both callers for every backend.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

structure Backend where
  mul : Nat → Nat → Nat → Prog isa
  suffix : String
  features : List String
  signVerified : Verified target (SignVerify.sign mul) (Spec.Dsa.signContract abi)
  verifyVerified : Verified target (SignVerify.verify mul) (Spec.Dsa.verifyContract abi)

end VG.Proof.Dsa.AArch64
