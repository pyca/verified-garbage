module
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract


/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic, its stack allowance and proofs of
the complete arithmetic callers. This admits both inline arithmetic and calls
to a shared kernel. The generic registration emits each caller for every backend.
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
  validateVerified : Verified target (Prevalidated.validate mul) (Spec.Dsa.validatePublicKeyContract abi stack)
  prevalidatedVerified : Verified target (Prevalidated.verify mul) (Spec.Dsa.verifyPrevalidatedContract abi stack)
  validateSp : (Prevalidated.validate mul).all (fun i => !isa.writesSp i) = true
  prevalidatedSp : (Prevalidated.verify mul).all (fun i => !isa.writesSp i) = true
  parametersVerified : Verified target (Generate.checkParameters mul) (Proof.Dsa.checkParametersContract abi stack)
  deriveVerified : Verified target (Generate.deriveKey mul) (Spec.Dsa.deriveKeyContract abi stack)
  parametersSp : (Generate.checkParameters mul).all (fun i => !isa.writesSp i) = true
  parametersDepth : 16 * (Generate.checkParameters mul).aarch64Depth ≤ stack
  deriveSp : (Generate.deriveKey mul).all (fun i => !isa.writesSp i) = true
  deriveDepth : 16 * (Generate.deriveKey mul).aarch64Depth ≤ stack
  signSp : (SignVerify.sign mul).all (fun i => !isa.writesSp i) = true
  signDepth : 16 * (SignVerify.sign mul).aarch64Depth ≤ stack
  stackBound : stack < 2 ^ 32
  verifySp : (SignVerify.verify mul).all (fun i => !isa.writesSp i) = true

end VG.Proof.Dsa.AArch64
