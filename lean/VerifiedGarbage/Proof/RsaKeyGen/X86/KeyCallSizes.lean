module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.IntervalCases

/-! # Shared key-generation arguments determine the native public environment -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def callEnvironment (s : State) : Environment where
  workspace := arg s 16
  capacity := (arg s 17).toNat
  out := fun i => if i < 7 then arg s (2 * i) else 0
  primeLength := (arg s 5).toNat
  exponent := arg s 14
  exponentLength := (arg s 15).toNat

structure CallSizes (s : State) : Prop where
  length : Spec.RsaKeyGen.primeLenValid (arg s 5).toNat
  modulus : (arg s 1).toNat = 2 * (arg s 5).toNat
  privateExponent : (arg s 3).toNat = (arg s 1).toNat
  q : (arg s 7).toNat = (arg s 5).toNat
  dp : (arg s 9).toNat = (arg s 5).toNat
  dq : (arg s 11).toNat = (arg s 5).toNat
  qi : (arg s 13).toNat = (arg s 5).toNat
  exponentLength : 1 ≤ (arg s 15).toNat ∧ (arg s 15).toNat ≤ 8
  capacity : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s 17).toNat

theorem call_sizes {s : State} (h : contract.pre s) : CallSizes s := by
  sig_pre [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> first
    | with_reducible assumption
    | (constructor <;> with_reducible assumption)

theorem CallSizes.outputLength {s : State} (h : CallSizes s) {i : Nat} (hi : i < 7) :
    (callEnvironment s).outputLength i = (arg s (2 * i + 1)).toNat := by
  interval_cases i
  · exact h.modulus.symm
  · exact (h.privateExponent.trans h.modulus).symm
  · rfl
  · exact h.q.symm
  · exact h.dp.symm
  · exact h.dq.symm
  · exact h.qi.symm

theorem CallSizes.argument {s : State} (h : CallSizes s) {i : Nat} (hi : i < 18) :
    (callEnvironment s).argument i = arg s i := by
  have modulus : BitVec.ofNat 32 (2 * (arg s 5).toNat) = arg s 1 := by
    rw [← h.modulus, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have privateExponent : BitVec.ofNat 32 (2 * (arg s 5).toNat) = arg s 3 := by
    rw [← h.modulus, ← h.privateExponent, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have same (j : Nat) (H : (arg s j).toNat = (arg s 5).toNat) :
      arg s 5 = arg s j := BitVec.eq_of_toNat_eq H.symm
  interval_cases i <;>
    simp only [Environment.argument, callEnvironment, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact modulus
  · exact privateExponent
  · exact same _ h.q
  · exact same _ h.dp
  · exact same _ h.dq
  · exact same _ h.qi

end VG.Proof.RsaKeyGen.X86.Key
