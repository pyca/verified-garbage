module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainPre
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The callable domain check implements the shared FFDH parameter contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domain_data (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 128).pre s) :
    ∃ p : Inputs, s.gpr .r3 = p.base ∧ s.gpr .r0 = p.domain ∧
      (s.gpr .r2).toNat = p.k ∧ (stackArg s 0).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧ DomainFnInput p s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := s.gpr .r3
    domain := s.gpr .r0
    publicValue := 0
    privateValue := 0
    output := 0
    entropy := 0
    len := (stackArg s 0).toNat
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
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, domain_input s original rfl rfl rfl rfl rfl⟩

theorem domain_correct (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkDomainContract abi 128).post s t := by
  obtain ⟨p, _, domain, count, _, bytes, input⟩ := domain_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := domainFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right, domain, count]
  change (t.gpr .r0).toNat = if Spec.Ffdh.domainValid p.k
    (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat) then 1 else 0
  rw [bytes, result, checkedDomainFlag_spec]
  split <;> rfl

end VG.Proof.Ffdh.Arm
