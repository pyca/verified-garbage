module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
import Mathlib.Tactic.IntervalCases

/-! # The shared key signature supplies native pointer bounds and permissions -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def callOutput (s : State) (i : Nat) : Region := ⟨(arg s (2 * i)).setWidth 64, (arg s (2 * i + 1)).toNat⟩
def callOutputs (s : State) : List Region := (List.range 7).map (callOutput s)
def callWorkspace (s : State) : Region := ⟨(arg s 16).setWidth 64, 8 * (arg s 17).toNat⟩
def callExponent (s : State) : Region := ⟨(arg s 14).setWidth 64, (arg s 15).toNat⟩
def callArguments (s : State) : Region := ⟨argAddr s 0, 72⟩

structure CallLayout (s : State) : Prop where
  low : 36 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  outputFit : ∀ i < 7, (arg s (2 * i)).toNat + (arg s (2 * i + 1)).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 16).toNat + 8 * (arg s 17).toNat ≤ 2 ^ 32
  exponentFit : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  wr : s.wr = callOutputs s ++ [callWorkspace s, callArguments s]
  rd : s.rd = [callExponent s]

theorem call_layout {s : State} (h : contract.pre s) : CallLayout s := by
  sig_pre [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor
  · with_reducible assumption
  · with_reducible assumption
  · intro i hi
    interval_cases i <;> with_reducible assumption
  · simpa only [Nat.mul_comm] using (show (arg s 16).toNat + (arg s 17).toNat * 8 ≤ 2 ^ 32 from by with_reducible assumption)
  · with_reducible assumption
  · simp only [callOutputs, callOutput, callWorkspace, callArguments, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append,
      Nat.reduceMul, Nat.reduceAdd]
    simp only [Nat.mul_comm] at *
    with_reducible assumption
  · change s.rd = [⟨(arg s 14).setWidth 64, (arg s 15).toNat⟩]
    assumption

theorem CallSizes.outputRegion {s : State} (h : CallSizes s) {i : Nat} (hi : i < 7) :
    (callEnvironment s).outputRegion i = callOutput s i := by
  unfold Environment.outputRegion callOutput
  rw [h.outputLength hi]
  simp only [callEnvironment, hi, ite_true]

theorem CallLayout.outFit {s : State} (h : CallLayout s) (sizes : CallSizes s) {i : Nat} (hi : i < 7) :
    ((callEnvironment s).out i).toNat + (callEnvironment s).outputLength i ≤ 2 ^ 32 := by
  rw [sizes.outputLength hi]
  simpa only [callEnvironment, hi, ite_true] using h.outputFit i hi

end VG.Proof.RsaKeyGen.X86.Key
