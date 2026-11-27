module
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Impl.Dsa.AArch64.Fn
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.DomainChecked
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Dsa.SignContractWith
public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim


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
  validateVerified : Verified target (Prevalidated.validate mul) (Spec.Dsa.validatePublicKeyContract abi stack)
  prevalidatedVerified : Verified target (Prevalidated.verify mul) (Spec.Dsa.verifyPrevalidatedContract abi stack)
  validateSp : (Prevalidated.validate mul).all (fun i => !isa.writesSp i) = true
  prevalidatedSp : (Prevalidated.verify mul).all (fun i => !isa.writesSp i) = true
  parametersVerified : Verified target (Generate.checkParameters mul) (Proof.Dsa.checkParametersContract abi stack)
  deriveVerified : Verified target (Generate.deriveKey mul) (Spec.Dsa.deriveKeyContract abi stack)
  parametersSp : (Generate.checkParameters mul).all (fun i => !isa.writesSp i) = true
  parametersNoDit : (Generate.checkParameters mul).all (fun i => !i.touchesDit) = true
  parametersDepth : 16 * (Generate.checkParameters mul).aarch64Depth ≤ stack
  deriveSp : (Generate.deriveKey mul).all (fun i => !isa.writesSp i) = true
  deriveDepth : 16 * (Generate.deriveKey mul).aarch64Depth ≤ stack
  signSp : (SignVerify.sign mul).all (fun i => !isa.writesSp i) = true
  signNoDit : (SignVerify.sign mul).all (fun i => !i.touchesDit) = true
  signDepth : 16 * (SignVerify.sign mul).aarch64Depth ≤ stack
  prevalidatedSignVerified : Verified target (PrevalidatedSign.sign mul)
    (signContractWith Spec.Dsa.validatePrivateKeyBytes abi stack)
  prevalidatedSignSp : (PrevalidatedSign.sign mul).all (fun i => !isa.writesSp i) = true
  prevalidatedSignNoDit : (PrevalidatedSign.sign mul).all (fun i => !i.touchesDit) = true
  prevalidatedSignDepth : 16 * (PrevalidatedSign.sign mul).aarch64Depth ≤ stack
  validatePrivateVerified : Verified target (PrevalidatedSign.validate mul)
    (Spec.Dsa.validatePrivateKeyContract abi stack)
  validatePrivateSp : (PrevalidatedSign.validate mul).all (fun i => !isa.writesSp i) = true
  deriveCheckedVerified : Verified target (Generate.deriveChecked mul)
    (Spec.Dsa.deriveKeyDomainCheckedContract abi stack)
  deriveCheckedSp : (Generate.deriveChecked mul).all (fun i => !isa.writesSp i) = true
  deriveCheckedNoDit : (Generate.deriveChecked mul).all (fun i => !i.touchesDit) = true
  deriveCheckedDepth : 16 * (Generate.deriveChecked mul).aarch64Depth ≤ stack
  stackBound : stack < 2 ^ 32
  /-- What the cleanup of each function that is emitted needs of its code with
  `mul` (`Scrub.scrubSide`, for the registers `Fn.clear` and the stack the
  function uses): proved where the backend is defined, by evaluating its
  code. -/
  validateScrub : Scrub.scrubSide (Prevalidated.validate mul) stack 32 Fn.clear [] = true
  prevalidatedScrub : Scrub.scrubSide (Prevalidated.verify mul) stack 32 Fn.clear [] = true
  validatePrivateScrub : Scrub.scrubSide (PrevalidatedSign.validate mul) stack 32 Fn.clear [] = true
  deriveScrub : Scrub.scrubSide (Generate.deriveKey mul) stack 32 Fn.clear [] = true
  randomSignScrub : Scrub.scrubSide
    (RandomSign.code ("vg_dsa_sign_prevalidated" ++ suffix) (PrevalidatedSign.sign mul)) (stack + 256) 32
    Fn.clear [] = true
  generateKeyScrub : Scrub.scrubSide
    (GenerateKey.code ("vg_dsa_check_parameters" ++ suffix) ("vg_dsa_derive_key_checked" ++ suffix)
      (Generate.checkParameters mul) (Generate.deriveChecked mul)) (stack + 256) 32 Fn.clear [] = true

end VG.Proof.Dsa.AArch64
