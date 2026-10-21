module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallLayout
import Mathlib.Tactic.IntervalCases

/-! # The shared key signature separates inputs, outputs and the reserved frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 36#64, 36⟩

structure CallSeparation (s : State) : Prop where
  outputScratch : ∀ i < 7, (callOutput s i).Disjoint (callWorkspace s)
  outputSeparate : ∀ i < 7, ∀ j < 7, i < j → (callOutput s i).Disjoint (callOutput s j)
  exponentScratch : (callExponent s).Disjoint (callWorkspace s)
  exponentOutput : ∀ i < 7, (callExponent s).Disjoint (callOutput s i)
  argsWorkspace : (callArguments s).Disjoint (callWorkspace s)
  stackOutput : ∀ i < 7, (callOutput s i).Disjoint (reservedRegion s)
  stackWorkspace : (callWorkspace s).Disjoint (reservedRegion s)
  stackExponent : (callExponent s).Disjoint (reservedRegion s)
  returnOutput : ∀ i < 7, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (callOutput s i)
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (callWorkspace s)

theorem call_separation {s : State} (h : contract.pre s) : CallSeparation s := by
  sig_pre [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor
  all_goals dsimp only [callOutput, callWorkspace, callExponent, callArguments, reservedRegion]
  all_goals simp only [Nat.mul_comm] at *
  · intro i hi
    interval_cases i
    all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · intro i hi j hj order
    interval_cases i <;> interval_cases j
    all_goals first | omega | with_reducible assumption
  · first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · intro i hi
    interval_cases i
    all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · intro i hi
    interval_cases i
    all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · intro i hi
    interval_cases i
    all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)
  · first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaKeyGen.X86.Key
