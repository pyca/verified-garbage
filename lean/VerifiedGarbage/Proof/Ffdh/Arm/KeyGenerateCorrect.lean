module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeySpec
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

theorem keyGenerate_correct (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.KeyGenerate.code prepare tail) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.generateKeyContract abi 176).post s t := by
  obtain ⟨p, rb, _, privateValue, publicValue, domain, count, _, entropy, domainBytes, entropyBytes, input⟩ := keyGenerate_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := keyGenerateFn_ok prepare tail prep law s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have randLength : (stackArg s 4).toNat = (stackArg s 2).toNat := by
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, randLength, _⟩ := pre
    exact randLength
  sig_post [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes entropyBytes
  simp only [randLength, count, domain, entropy, domainBytes, entropyBytes, privateValue, publicValue]
  intro valid
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  exact keyResult_spec input.size valid (result modValid)

end VG.Proof.Ffdh.Arm
