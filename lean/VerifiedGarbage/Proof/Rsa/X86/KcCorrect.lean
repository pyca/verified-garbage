module

public import VerifiedGarbage.Proof.Rsa.X86.KcReturn

/-! # Both i686 key-check operations satisfy their existing shared contracts -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Dsa.X86

private theorem bool_result (b : Bool) : BitVec.ofNat 32 b.toNat = (if b then 1 else 0) := by
  cases b <;> rfl

theorem correct (full : Bool) (s : State) (h : (contract full).pre s) :
    ∃ trace t, Exec isa (VG.Impl.Rsa.X86.KeyCheck.code full) s trace t ∧ abiPreserved s t ∧
      (contract full).post s t := by
  have a := abi_of h
  obtain ⟨trace, t, run, value, preserved⟩ := operation_ok a
  refine ⟨trace, t, run, preserved, ?_⟩
  cases full
  · change (Spec.Rsa.checkCrtKeyContract abi 20).post s t
    sig_post [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    simp only [validity, numbers, caller, inputBytes, CallGeometry.buffer, Bool.false_eq_true, ite_false] at value
    have dp : (arg s 9).toNat = (arg s 5).toNat := a.dpLen
    have dq : (arg s 11).toNat = (arg s 7).toNat := a.dqLen
    have qi : (arg s 13).toNat = (arg s 5).toNat := a.qiLen
    simp only [Nat.reduceAdd, Nat.reduceMul] at value
    rw [dp, dq, qi] at value
    unfold Spec.Rsa.checkCrtKey
    rw [value]
    rw [VG.Proof.Bignum.bytesAt_length]
    exact bool_result _
  · change (Spec.Rsa.checkKeyContract abi 20).post s t
    sig_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    simp only [validity, numbers, caller, inputBytes, CallGeometry.buffer, ite_true] at value
    have dp : (arg s 11).toNat = (arg s 7).toNat := a.dpLen
    have dq : (arg s 13).toNat = (arg s 9).toNat := a.dqLen
    have qi : (arg s 15).toNat = (arg s 7).toNat := a.qiLen
    simp only [Nat.reduceAdd, Nat.reduceMul] at value
    rw [dp, dq, qi] at value
    unfold Spec.Rsa.checkKey
    rw [value]
    rw [VG.Proof.Bignum.bytesAt_length]
    exact bool_result _
end VG.Proof.Rsa.X86.KeyCheck
