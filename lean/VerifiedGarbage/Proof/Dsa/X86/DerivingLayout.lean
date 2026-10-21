module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
public import VerifiedGarbage.Proof.Dsa.X86.DerivingResources
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! # Public call layout obtained from installed domain arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def derivingInputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen),
    (.input .nonce, qLen), (.input .p, 2 * pLen + qLen)]

def derivingPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 2
  | .input .q => arg s 2 + arg s 4
  | .input .g => arg s 2 + arg s 4 + arg s 6
  | .input .nonce => arg s 5
  | _ => 0

def derivingParams (s : State) : Spec.Dsa.Params := Spec.Dsa.paramsBytes (arg s 4).toNat (arg s 6).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)

def derivingLayout (s : State) (A : DerivingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 7
  size := (arg s 8).toNat * 8
  pLen := (arg s 4).toNat
  qLen := (arg s 6).toNat
  p := (derivingParams s).p
  q := (derivingParams s).q
  widths := A.lengths
  extent := A.used
  inputs := derivingInputs (arg s 4).toNat (arg s 6).toNat
  pointers := derivingPointers s
  stable := by
    intro input hi
    simp only [derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 4).toNat (Spec.Dsa.bitLength (derivingParams s).q / 8)

theorem derivingInputs_shape (pLen qLen : Nat) :
    ∀ input ∈ derivingInputs pLen qLen, ShapePointer input.1 := by
  intro input hi
  simp only [derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem derivingInstalled_ready {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t) :
    ShapeCallReady (derivingLayout s A) (arg s 4).toNat t := by
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (2, .p) ∈ Generate.deriveArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨X, _⟩ := I.input (by decide : (5, .nonce) ∈ Generate.deriveArguments) A.scalarBound
    (by rw [A.rd, A.wr]; simp) A.scalarScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowScalar.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_,
    congrArg BitVec.toNat (I.arguments (4, .digestLen) (by decide))⟩
  · intro input hi
    simp only [derivingLayout, derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact X
    · change CallerBuffer t _ _ (.input .p) (2 * (arg s 4).toNat + (arg s 6).toNat)
      rw [← A.keyLength]; exact Params
  · intro input hi
    simp only [derivingLayout, derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact I.arguments (2, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
    · exact I.arguments (5, .nonce) (by decide)
    · exact I.arguments (2, .p) (by decide)
  · exact (congrArg (fun k : Spec.Dsa.Params => k.p) Value).symm
  · exact (congrArg (fun k : Spec.Dsa.Params => k.q) Value).symm

theorem derivingLayout_eq {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q) : derivingLayout s A = derivingLayout t B := by
  have A0 := args 2 (by decide)
  have A2 := args 4 (by decide)
  have A3 := args 6 (by decide)
  have A4 := args 7 (by decide)
  have A5 := args 8 (by decide)
  have Ax := args 5 (by decide)
  have pointers : derivingPointers s = derivingPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [derivingPointers, A0, A2, A3, Ax]
    | «local» d => rfl
    | signatureS => rfl
  simp only [derivingLayout, SP, argumentPointer, A2, A3, A4, A5, P, Q, pointers]

theorem derivingInstalled_output {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t) :
    KeyOutputReady (derivingLayout s A) (arg s 0) t := by
  refine ⟨I.arguments (0, .out) (by decide), ?_, ?_, ?_⟩
  · intro i hi
    change i < 3 * (arg s 4).toNat + 2 * (arg s 6).toNat at hi
    rw [I.keeps.2.2, A.wr]
    refine ⟨_, List.mem_cons_self, Offset.contains_base _ ?_ ?_⟩
    · have := A.outLength; omega
    · have := A.outBound; have := A.outLength; omega
  · change Region.Disjoint ⟨(pointerValue (argumentPointer s 7) t (.input .p)).setWidth 64, 2 * (arg s 4).toNat + (arg s 6).toNat⟩
      ⟨argumentPointer s 0, 3 * (arg s 4).toNat + 2 * (arg s 6).toNat⟩
    rw [I.arguments (2, .p) (by decide), ← A.keyLength, ← A.outLength]
    exact A.keyOut
  · change Region.Disjoint ⟨(pointerValue (argumentPointer s 7) t (.input .nonce)).setWidth 64, (arg s 6).toNat⟩
      ⟨argumentPointer s 0, 3 * (arg s 4).toNat + 2 * (arg s 6).toNat⟩
    rw [I.arguments (5, .nonce) (by decide), ← A.outLength]
    exact A.scalarOut

end VG.Proof.Dsa.X86
