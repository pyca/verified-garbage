module

import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangePre
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeFn
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangePrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.TCB.Arm.Isa

/-! The callable shared-secret computation satisfies the architecture-independent contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem data (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ stackArg s 3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧
      (stackArg s 0).toNat = p.k ∧ (stackArg s 6).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ FnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 5
    domain := s.gpr .r2
    publicValue := stackArg s 3
    privateValue := stackArg s 1
    output := s.gpr .r0
    entropy := 0
    len := (stackArg s 6).toNat
    k := (stackArg s 0).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((s.gpr .r3).toNat = 3 * (stackArg s 0).toNat)
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
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 0).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem correct (backend : MontBackend) (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s) :
    ∃ tr t, Exec isa (code backend) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.exchangeContract abi 176).post s t := by
  obtain ⟨p, yb, xb, _, out, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := fn_ok backend s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have lengths : (s.gpr .r1).toNat = (stackArg s 0).toNat ∧
      (stackArg s 4).toNat = (stackArg s 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, outLen, yLen, _, _, _⟩ := pre
    exact ⟨outLen, yLen⟩
  sig_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [lengths.1, lengths.2, count, domain, peer, scalar, privateCount, domainBytes,
    peerBytes, scalarBytes, out]
  intro valid validPeer
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  exact exchangeResult_spec valid validPeer (result modValid)

end VG.Proof.Ffdh.Arm.SharedExchange
