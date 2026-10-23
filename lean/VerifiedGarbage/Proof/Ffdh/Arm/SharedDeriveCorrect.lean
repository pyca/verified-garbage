module

import VerifiedGarbage.Proof.Ffdh.Arm.SharedDerivePre
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveFn
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.Arm.Target

/-! The callable derivation satisfies the architecture-independent contract: its status is
`keyStatus`, since a power of the checked generator is in its subgroup. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem scalar_iff (p : Inputs) (x : Nat) :
    Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) x = true ↔ 0 < x ∧ x < scalarBound p := by
  unfold Spec.Ffdh.privateValid scalarBound
  rw [p.domainP, p.domainQ]
  by_cases hasQ : p.hasQ = true <;> simp [hasQ]

/-- The status tells whether the scalar is in range, for any domain. -/
theorem keyStatus_two_iff (p : Inputs) (x : Nat) :
    Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) x = 2 ↔ ¬ (0 < x ∧ x < scalarBound p) := by
  rw [← scalar_iff p x]
  unfold Spec.Ffdh.keyStatus
  cases Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, not_true_eq_false, iff_false]
    split <;> decide

theorem status_spec (p : Inputs) (xb : List Byte) (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (status p xb).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) ∧
      (accepted p xb ↔ Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) = 1) := by
  have parameters : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom) = true := by
    have h := valid
    rw [Spec.Ffdh.domainValid, Bool.and_eq_true] at h
    exact h.1
  have scalar := scalar_iff p (Spec.Rsa.os2ip xb)
  have power := VG.Proof.Ffdh.publicValid_power parameters (Spec.Rsa.os2ip xb)
  rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq parameters]
  rw [p.domainP, p.domainG] at power ⊢
  have shared : sharedAccepted p (gOctets p) xb = true ↔
      1 < p.G ^ Spec.Rsa.os2ip xb % p.P ∧ p.G ^ Spec.Rsa.os2ip xb % p.P < p.P - 1 := by
    simp only [sharedAccepted, sharedValue, gOctets, VG.Proof.Bignum.powMod_eq, decide_eq_true_eq]
    rfl
  unfold status accepted
  by_cases range : 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p
  · have pv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) = true :=
      scalar.mpr range
    rw [ite_eq_left range, pv]
    by_cases acc : sharedAccepted p (gOctets p) xb = true
    · have pub := power.mpr (shared.mp acc)
      simp [acc, pub, range]
    · have pub : ¬ Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom, p.G ^ Spec.Rsa.os2ip xb % p.P⟩ = true :=
        fun h => acc (shared.mpr (power.mp h))
      simp [acc, pub, range]
  · have pv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) = false := by
      cases e : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb)
      · rfl
      · exact (range (scalar.mp e)).elim
    rw [ite_eq_right range, pv]
    simp [range]

theorem data (s : State) (pre : (Spec.Ffdh.derivePublicContract abi 176).pre s) :
    ∃ (p : Inputs) (xb : List Byte), stackArg s 3 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ stackArg s 1 = p.privateValue ∧ p.publicValue = p.domain ∧
      (stackArg s 0).toNat = p.k ∧ (stackArg s 4).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ FnInput p xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 3
    domain := s.gpr .r2
    publicValue := s.gpr .r2
    privateValue := stackArg s 1
    output := s.gpr .r0
    entropy := 0
    len := (stackArg s 4).toNat
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
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    input s original (p := p) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem correct (backend : MontBackend) (s : State) (pre : (Spec.Ffdh.derivePublicContract abi 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.SharedDerive.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.derivePublicContract abi 176).post s t := by
  obtain ⟨p, xb, _, out, domain, scalar, _, count, _, privateCount, domainBytes, scalarBytes, input⟩ :=
    data s pre
  obtain ⟨tr, t, run, preserved, res⟩ := fn_ok backend s input
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes scalarBytes
  simp only [count, domain, scalar, privateCount, domainBytes, scalarBytes, out]
  intro valid
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  obtain ⟨status_t, bytes⟩ := res modValid
  obtain ⟨statusEq, acceptedIff⟩ := status_spec p xb valid
  refine ⟨by rw [status_t]; exact statusEq, ?_⟩
  simp only [State.addr] at bytes
  by_cases acc : accepted p xb
  · rw [ite_eq_left (acceptedIff.mp acc), bytes, ite_eq_left acc]
    rfl
  · rw [ite_eq_right (fun h => acc (acceptedIff.mpr h)), bytes, ite_eq_right acc]

end VG.Proof.Ffdh.Arm.SharedDerive
