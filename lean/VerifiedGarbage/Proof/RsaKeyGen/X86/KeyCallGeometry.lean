module

import VerifiedGarbage.Proof.RsaKeyGen.X86.DisjointBounds
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaKeyGen.X86.KeyCallValid`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCallSeparation`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCallSizes`, which this module and modules that import it used -/

section

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
  sig_pre [contract, keyStack, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig,
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

end

end

/-! # The shared key signature separates inputs, outputs and the reserved frame -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyCallLayout.lean`, which only this module imported.
section

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
  low : 68 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  outputFit : ∀ i < 7, (arg s (2 * i)).toNat + (arg s (2 * i + 1)).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 16).toNat + 8 * (arg s 17).toNat ≤ 2 ^ 32
  exponentFit : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  wr : s.wr = callOutputs s ++ [callWorkspace s, callArguments s]
  rd : s.rd = [callExponent s]

theorem call_layout {s : State} (h : contract.pre s) : CallLayout s := by
  sig_pre [contract, keyStack, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig,
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 68#64, 68⟩

structure CallSeparation (s : State) : Prop where
  outputScratch : ∀ i < 7, (callOutput s i).Disjoint (callWorkspace s)
  outputSeparate : ∀ i < 7, ∀ j < 7, i < j → (callOutput s i).Disjoint (callOutput s j)
  exponentScratch : (callExponent s).Disjoint (callWorkspace s)
  exponentOutput : ∀ i < 7, (callExponent s).Disjoint (callOutput s i)
  argsWorkspace : (callArguments s).Disjoint (callWorkspace s)
  argsOutput : ∀ i < 7, (callArguments s).Disjoint (callOutput s i)
  stackOutput : ∀ i < 7, (callOutput s i).Disjoint (reservedRegion s)
  stackWorkspace : (callWorkspace s).Disjoint (reservedRegion s)
  stackExponent : (callExponent s).Disjoint (reservedRegion s)
  returnOutput : ∀ i < 7, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (callOutput s i)
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (callWorkspace s)

theorem call_separation {s : State} (h : contract.pre s) : CallSeparation s := by
  sig_pre [contract, keyStack, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig,
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

end

end

/-! # The shared precondition establishes the native key environment -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem call_valid {s : State} (h : contract.pre s) : (callEnvironment s).Valid := by
  have Z := call_sizes h
  have A := call_layout h
  have D := call_separation h
  refine ⟨Z.length, Z.exponentLength, ?_, A.workspaceFit, ?_, A.exponentFit, ?_, ?_, D.exponentScratch, ?_⟩
  · change Spec.Rsa.scratchWords (2 * (arg s 5).toNat) ≤ (arg s 17).toNat
    rw [← Z.modulus]
    exact Z.capacity
  · intro i hi
    exact A.outFit Z hi
  · intro i hi
    rw [Z.outputRegion hi]
    exact D.outputScratch i hi
  · intro i hi j hj different
    rw [Z.outputRegion hi, Z.outputRegion hj]
    by_cases order : i < j
    · exact D.outputSeparate i hi j hj order
    · exact (D.outputSeparate j hj i hi (by omega_using [different, order])).symm
  · intro i hi
    rw [Z.outputRegion hi]
    exact D.exponentOutput i hi

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The shared reserved frame supplies the native arithmetic stack gap -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86

def callSp (s : State) : BitVec 32 := s.gpr .esp - 16#32

theorem CallLayout.privateNat {s : State} (A : CallLayout s) :
    (callSp s).toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by have := A.low; omega_using [this])

theorem CallLayout.reservedNat {s : State} (A : CallLayout s) :
    (reservedRegion s).base.toNat = (s.gpr .esp).toNat - 68 := by
  change ((s.gpr .esp).setWidth 64 - 68#64).toNat = _
  rw [← Taint.sub_setWidth A.low, BitVec.toNat_setWidth, sub_toNat A.low,
    Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])]

theorem workspace_stack {s : State} (h : contract.pre s) :
    StkOk (callSp s) (callEnvironment s).base (callEnvironment s).size := by
  have A := call_layout h
  have D := call_separation h
  have v := call_valid h
  have bank := v.bankFit
  have positive : 0 < (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega_using [bank]
  have bounds := disjoint_bounds positive (by decide : 0 < 68) D.stackWorkspace
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (reservedRegion s).base.toNat ∨
    (reservedRegion s).base.toNat + 68 ≤ (callEnvironment s).base.toNat at bounds
  rw [A.reservedNat] at bounds
  change 20 ≤ (callSp s).toNat ∧
    ((callSp s).toNat ≤ (callEnvironment s).base.toNat ∨
      (callEnvironment s).base.toNat + (callEnvironment s).size + 20 ≤ (callSp s).toNat)
  rw [A.privateNat]
  have := A.low
  omega_using [bounds, this]

theorem workspace_deep {s : State} (h : contract.pre s) :
    KeyArgs.DeepStk (callSp s) (callEnvironment s).base (callEnvironment s).size := by
  have A := call_layout h
  have D := call_separation h
  have v := call_valid h
  have bank := v.bankFit
  have positive : 0 < (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega_using [bank]
  have bounds := disjoint_bounds positive (by decide : 0 < 68) D.stackWorkspace
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (reservedRegion s).base.toNat ∨
    (reservedRegion s).base.toNat + 68 ≤ (callEnvironment s).base.toNat at bounds
  rw [A.reservedNat] at bounds
  change 52 ≤ (callSp s).toNat ∧ (callSp s).toNat + 92 ≤ 2 ^ 32 ∧
    ((callSp s).toNat ≤ (callEnvironment s).base.toNat ∨
      (callEnvironment s).base.toNat + (callEnvironment s).size + 52 ≤ (callSp s).toNat)
  rw [A.privateNat]
  have := A.low
  have := A.argsFit
  omega_arith

theorem CallLayout.savedSub {s : State} (A : CallLayout s) :
    (⟨(callSp s).setWidth 64, 16⟩ : Region).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 68 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_sub (by decide) A.low

end VG.Proof.RsaKeyGen.X86.Key
