module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCorrect
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.TCB.Arm.Isa

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

/-! The complete callable key-generation attempt satisfies the shared contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerate_data (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyGenerateFnInput p rb s := by
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, old⟩ := key_data s (keyGenerate_pre128 s pre)
  exact ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, keyGenerate_input s pre base privateValue publicValue domain count capacity
      entropy old.outputY old.privateLength domainBytes entropyBytes⟩

end VG.Proof.Ffdh.Arm
