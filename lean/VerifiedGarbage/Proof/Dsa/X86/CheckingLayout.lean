module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.CheckingResources
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! # Public call layout obtained from installed domain arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def checkingInputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen)]

def checkingPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 0
  | .input .q => arg s 0 + arg s 2
  | .input .g => arg s 0 + arg s 2 + arg s 3
  | _ => 0

def checkingParams (s : State) : Spec.Dsa.Params := Spec.Dsa.paramsBytes (arg s 2).toNat (arg s 3).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)

def checkingLayout (s : State) (A : CheckingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 4
  size := (arg s 5).toNat * 8
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  p := (checkingParams s).p
  q := (checkingParams s).q
  widths := A.lengths
  extent := A.used
  inputs := checkingInputs (arg s 2).toNat (arg s 3).toNat
  pointers := checkingPointers s
  stable := by
    intro input hi
    simp only [checkingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 2).toNat (Spec.Dsa.bitLength (checkingParams s).q / 8)

theorem checkingInputs_shape (pLen qLen : Nat) :
    ∀ input ∈ checkingInputs pLen qLen, ShapePointer input.1 := by
  intro input hi
  simp only [checkingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem checkingInstalled_ready {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t) :
    ShapeCallReady (checkingLayout s A) (arg s 2).toNat t := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_,
    congrArg BitVec.toNat (I.arguments (2, .digestLen) (by decide))⟩
  · intro input hi
    simp only [checkingLayout, checkingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
  · intro input hi
    simp only [checkingLayout, checkingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact I.arguments (0, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
  · exact (congrArg (fun k : Spec.Dsa.Params => k.p) Value).symm
  · exact (congrArg (fun k : Spec.Dsa.Params => k.q) Value).symm

theorem checkingLayout_eq {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (checkingParams s).p = (checkingParams t).p)
    (Q : (checkingParams s).q = (checkingParams t).q) : checkingLayout s A = checkingLayout t B := by
  have A0 := args 0 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have pointers : checkingPointers s = checkingPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [checkingPointers, A0, A2, A3]
    | «local» d => rfl
    | signatureS => rfl
  simp only [checkingLayout, SP, argumentPointer, A2, A3, A4, A5, P, Q, pointers]

end VG.Proof.Dsa.X86
