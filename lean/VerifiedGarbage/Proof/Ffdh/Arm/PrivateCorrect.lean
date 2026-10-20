module

import VerifiedGarbage.Proof.Ffdh.Arm.PrivatePre
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! Native callable imported-private-key validation satisfies the shared FFDH result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem private_data (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 3 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧ (s.gpr .r2).toNat = p.k ∧
      (stackArg s 4).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ PrivateFnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 3
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := stackArg s 1
    output := 0
    entropy := 0
    len := (stackArg s 4).toNat
    k := (s.gpr .r2).toNat
    privateLength := (stackArg s 2).toNat
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
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    private_input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem private_correct (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPrivateContract abi 128).post s t := by
  obtain ⟨p, yb, xb, _, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := private_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := privateFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have length : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := pre
    exact length
  sig_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [length, count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes]
  intro valid
  rw [result]
  exact checkedPrivateFlag_spec p yb xb valid

end VG.Proof.Ffdh.Arm
