module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic, its stack allowance and proofs of
the complete callers. This admits both inline arithmetic and calls to a
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
  parametersVerified : Verified target (Generate.checkParameters sq mul) (Proof.Dsa.checkParametersContract abi stack)
  deriveVerified : Verified target (Generate.deriveKey sq mul) (Spec.Dsa.deriveKeyContract abi stack)
  parametersSp : (Generate.checkParameters sq mul).all (fun i => !isa.writesSp i) = true
  deriveSp : (Generate.deriveKey sq mul).all (fun i => !isa.writesSp i) = true
  parametersDepth : (Generate.checkParameters sq mul).x86_64Depth ≤ stack
  deriveDepth : (Generate.deriveKey sq mul).x86_64Depth ≤ stack
  stackBound : stack < 2 ^ 32

end VG.Proof.Dsa.X86_64
