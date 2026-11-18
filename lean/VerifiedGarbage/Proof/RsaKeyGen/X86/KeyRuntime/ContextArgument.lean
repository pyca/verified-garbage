module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.DisjointBounds
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
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
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Spec.RsaKeyGen
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentBranch
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `RsaKeyGen.X86.KeyOutputReady`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyInputPair`, which only this module used -/

section

/-! # Retained public key arguments determine the register state used by imports and exports -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure InputPair (E : Environment) (s t : State) : Prop where
  left : Input E s
  right : Input E t
  stack : s.gpr .esp = t.gpr .esp

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyDSelectTiming`, which this module and modules that import it used -/

section

/-! # Public exponent branches compose with secret native arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key

theorem key_public_trace {c : Prog isa} (H : KeyPublic c) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) c
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  obtain ⟨hint, out, checked, lower⟩ := H
  exact checkedProgramChange checked lower

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRetryFlag`, which this module and modules that import it used -/

section

/-! # The secret native retry comparison equals the released shared result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/Retry.lean`, which only this module imported.
section

/-! # The released retry status identifies exactly the small private inverse -/

section
namespace VG.Proof.RsaKeyGen
open VG

theorem keyFromPrimes_retry_iff (nlen e p q : Nat) :
    Spec.RsaKeyGen.keyFromPrimes nlen e p q = .inr () ↔
      ∃ d, Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) = some d ∧ d ≤ 2 ^ (nlen / 2) := by
  have sorted : (if p < q then (q, p) else (p, q)) = (max p q, min p q) := by
    by_cases order : p < q
    · simp only [order, ite_true, Nat.max_eq_right (Nat.le_of_lt order), Nat.min_eq_left (Nat.le_of_lt order)]
    · simp only [order, ite_false, Nat.max_eq_left (by omega : q ≤ p), Nat.min_eq_right (by omega : q ≤ p)]
  unfold Spec.RsaKeyGen.keyFromPrimes
  rw [sorted]
  dsimp only
  cases inv : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
  | none => simp
  | some d =>
    dsimp only
    by_cases small : d ≤ 2 ^ (nlen / 2)
    · simp [small]
    · rw [ite_eq_right small]
      cases other : Spec.Rsa.inverse (min p q) (max p q) with
      | none => simp [small]
      | some qi =>
        dsimp only
        split <;> simp [small]

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem KeyReady.retry_iff {B : Addr} {n e p q : Nat} {m : Mem} (R : KeyReady B n e p q m) :
    (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n)) ↔
      Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr () := by
  rw [VG.Proof.RsaKeyGen.keyFromPrimes_retry_iff, show 32 * n / 2 = 16 * n by omega_using [], R.inverse]
  by_cases zero : slot m B kOk = 0
  · simp only [zero, ite_true, reduceCtorEq, false_and, exists_false]
  · have one : slot m B kOk = 1 := by have := R.bit; omega_using [zero, this]
    simp [one]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyWritePortTiming`, which this module and modules that import it used -/

section

/-! # Masked key output uses only public pointers and byte lengths in its trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def OutputPair (E : Environment) (s t : State) : Prop :=
  InputPair E s t ∧ VG.X86.Taint.Agree (workspaceTaint true) s t ∧
    slot s.mem E.base kOk ≤ 1 ∧ slot t.mem E.base kOk ≤ 1

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyImportedPair`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyLoadInputs`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCorePair`, which this module and modules that import it used -/

section

/-! # Two secret factor pairs reach the retry comparison with the same public state -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyPrepareTiming.lean`, which only this module imported.
section

/-! # Sorted factors and LCM feed only the public exponent into control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure Preparation (B : Addr) (Z n k e : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  pBound : num s.mem B n aPa < 2 ^ (32 * k)
  qBound : num s.mem B n aQa < 2 ^ (32 * k)
  zero : num s.mem B n aZero = 0
  one : num s.mem B n aOne = 1
  exponent : val32 s.mem B kEv 2 = e
  loaded : num s.mem B n aE = e

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key

structure CoreStart (B : Addr) (Z n k e p q : Nat) (s : State) : Prop extends Preparation B Z n k e s where
  pValue : num s.mem B n aPa = p
  qValue : num s.mem B n aQa = q

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The complete native input prefix initializes the arithmetic and imports its original inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def inputExponent (E : Environment) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
def inputPrime (E : Environment) (m : Mem) (i : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion i).base (E.outputRegion i).len)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Secret input snapshots are imported into native arithmetic with matching public state -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86

structure SizedStart (E : Environment) (e p q p' q' : Nat) (s t : State) : Prop where
  inputs : InputPair E s t
  leftExponent : inputExponent E s.mem = e
  rightExponent : inputExponent E t.mem = e
  leftP : inputPrime E s.mem 2 = p
  leftQ : inputPrime E s.mem 3 = q
  rightP : inputPrime E t.mem 2 = p'
  rightQ : inputPrime E t.mem 3 = q'

structure ImportedPair (E : Environment) (e p q p' q' : Nat) (s t : State) : Prop where
  inputs : InputPair E s t
  left : CoreStart E.base E.size E.n E.k e p q s
  right : CoreStart E.base E.size E.n E.k e p' q' t
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Completed numeric key derivation retains the public output environment and a boolean validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem core_mask_bit {B : Addr} {n e p q : Nat} {m : Mem} (R : CoreOutcome B n e p q m) :
    slot m B kOk ≤ 1 := by
  unfold CoreOutcome at R
  split at R <;> omega

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyCallGeometry`, which the modules that import this one used -/

section

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

end

end

/-! # Original cdecl arguments remain the runtime arithmetic's public widths -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (stackAddress stackValue)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

theorem context_argument {B : Addr} {Z i : Nat} {p : BitVec 32} {args : Nat → BitVec 32} {s : State}
    (C : Context B Z p args s) (index : i < 18) : CallArgument s B Z (i + 4) (args i) := by
  have operand : VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i =
      VG.Impl.Bignum.X86.PublicFn.argument (i + 4) := by
    unfold VG.Impl.RsaKeyGen.X86.CandidateArgs.arg VG.Impl.Bignum.X86.PublicFn.argument
    congr 1
    omega_using []
  have R := C.read i index
  rw [operand] at R
  have read : s.load32 (stackAddress s (i + 4)) = some (args i) := R
  have access : InRegions (s.rd ++ s.wr) (stackAddress s (i + 4)) 4 := by
    unfold State.load32 at read
    split at read
    · assumption
    · contradiction
  have value : stackValue s (i + 4) = args i := by
    unfold State.load32 at read
    rw [ite_eq_left access] at read
    exact Option.some.inj read
  have address : stackAddress s (i + 4) = off (argsRegion p).base (4 * i) := by
    rw [← C.address index, operand]
    rfl
  refine ⟨⟨access, ?_⟩, value⟩
  rw [address]
  exact C.separate.sub_left (Offset.sub_base _ (by change 4 * i + 4 ≤ 72; omega_using [index]))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
