module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
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

open VG.Spec.Rsa (bytesAt) in
/-- `signContract` under an extra precondition `valid` on the exact packed
key bytes: with `fun _ _ _ => true` it is `signContract`, with
`validatePrivateKeyBytes` the contract of a signing attempt for a validated
private key. Its result and leakage are `signContract`'s. -/
def signContractWith (valid : Nat → Nat → List Byte → Bool) {M : ISA} (A : Abi M) (stack : Nat := 0) :
    Contract M :=
  Spec.Dsa.signSig.contract A
    (pre := fun _out outLen key keyLen pLen _nonce qLen _digest _digestLen _scratch scratchLen m =>
      Spec.Dsa.lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        Spec.Dsa.scratchWords pLen.toNat ≤ scratchLen.toNat ∧
        valid pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat) = true)
    (post := fun out outLen key keyLen pLen nonce qLen digest digestLen _scratch _scratchLen m m' r =>
      let res := Spec.Dsa.signBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m nonce qLen.toNat) (bytesAt m digest digestLen.toNat)
      r.toNat = Spec.Dsa.signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen key keyLen pLen nonce qLen digest digestLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      Spec.Dsa.publicBytesLeak pLen.toNat qLen.toNat kb ++
        [Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen.toNat qLen.toNat kb
          (bytesAt m nonce qLen.toNat) (bytesAt m digest digestLen.toNat))])

structure Backend where
  sq : Prog isa
  mul : Nat → Nat → Nat → Prog isa
  stack : Nat := 0
  suffix : String
  features : List String
  signVerified : Verified target (SignVerify.sign sq mul) (Spec.Dsa.signContract abi stack)
  signSp : (SignVerify.sign sq mul).all (fun i => !isa.writesSp i) = true
  validateVerified : Verified target (Prevalidated.validate sq mul) (Spec.Dsa.validatePublicKeyContract abi stack)
  prevalidatedVerified : Verified target (Prevalidated.verify sq mul) (Spec.Dsa.verifyPrevalidatedContract abi stack)
  validateSp : (Prevalidated.validate sq mul).all (fun i => !isa.writesSp i) = true
  prevalidatedSp : (Prevalidated.verify sq mul).all (fun i => !isa.writesSp i) = true
  signDepth : (SignVerify.sign sq mul).x86_64Depth ≤ stack
  parametersVerified : Verified target (Generate.checkParameters sq mul) (Proof.Dsa.checkParametersContract abi stack)
  deriveVerified : Verified target (Generate.deriveKey sq mul) (Spec.Dsa.deriveKeyContract abi stack)
  parametersSp : (Generate.checkParameters sq mul).all (fun i => !isa.writesSp i) = true
  deriveSp : (Generate.deriveKey sq mul).all (fun i => !isa.writesSp i) = true
  parametersDepth : (Generate.checkParameters sq mul).x86_64Depth ≤ stack
  deriveDepth : (Generate.deriveKey sq mul).x86_64Depth ≤ stack
  prevalidatedSignVerified : Verified target (PrevalidatedSign.sign sq mul)
    (signContractWith Spec.Dsa.validatePrivateKeyBytes abi stack)
  prevalidatedSignSp : (PrevalidatedSign.sign sq mul).all (fun i => !isa.writesSp i) = true
  prevalidatedSignDepth : (PrevalidatedSign.sign sq mul).x86_64Depth ≤ stack
  validatePrivateVerified : Verified target (PrevalidatedSign.validate sq mul)
    (Spec.Dsa.validatePrivateKeyContract abi stack)
  validatePrivateSp : (PrevalidatedSign.validate sq mul).all (fun i => !isa.writesSp i) = true
  stackBound : stack < 2 ^ 32

end VG.Proof.Dsa.X86_64
