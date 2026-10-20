module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyPre
import VerifiedGarbage.Proof.Ffdh.Arm.KeySpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFn
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.TCB.Arm.Isa

/-! The complete callable key-generation attempt satisfies the shared contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem key_data (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 128).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyFnInput p rb s := by
  have original := pre
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  have domLength : dom.length = (stackArg s 1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 5
    domain := stackArg s 0
    publicValue := s.gpr .r2
    privateValue := s.gpr .r0
    output := s.gpr .r2
    entropy := stackArg s 3
    len := (stackArg s 6).toNat
    k := (stackArg s 2).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((stackArg s 1).toNat = 3 * (stackArg s 2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let rb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 2).toNat
  exact ⟨p, rb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    key_input s original (p := p) (rb := rb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem key_correct (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.generateKeyContract abi 128).post s t := by
  obtain ⟨p, rb, _, privateValue, publicValue, domain, count, _, entropy, domainBytes, entropyBytes, input⟩ := key_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := keyFn_ok s input
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
