module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The native callable public check satisfies the shared FFDH result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublic_data (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s) :
    ∃ (p : Inputs) (yb : List Byte), stackArg s 1 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ (s.gpr .r2).toNat = p.k ∧ (stackArg s 2).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧ CheckPublicFnInput p yb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, yLen, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 1
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := 0
    output := 0
    entropy := 0
    len := (stackArg s 2).toNat
    k := (s.gpr .r2).toNat
    privateLength := 0
    hasQ := decide ((s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rcases domainLen with h | h
        · exact h
        · contradiction }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  exact ⟨p, yb, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    checkPublic_input s original (p := p) (yb := yb) rfl rfl rfl rfl rfl rfl rfl⟩

theorem checkPublic_correct (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.CheckPublic.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPublicContract abi 128).post s t := by
  obtain ⟨p, yb, _, domain, value, count, _, domainBytes, valueBytes, input⟩ := checkPublic_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := checkPublicFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have yLen : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    exact pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_post [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  change Spec.Ffdh.domainValid (s.gpr .r2).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) = true → _
  rw [domain, domainBytes, count]
  intro valid
  rw [yLen, count, value]
  change (t.gpr .r0).toNat = if Spec.Ffdh.publicValid
    ⟨Spec.Ffdh.domainOf p.k (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat),
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k)⟩ then 1 else 0
  rw [domainBytes, valueBytes, result, checkedPublicFlag_spec p (Spec.Rsa.os2ip yb) valid]
  split <;> rfl

end VG.Proof.Ffdh.Arm
