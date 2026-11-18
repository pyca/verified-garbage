module

public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.CheckingEntry
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! ### `Dsa.X86.CheckingLayout`, which this module and modules that import it used -/

section

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
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega_using [this]) Bytes Qptr Gptr
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

end

end

/-! # Whole domain-checking traces from common public arguments and domain values -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CheckingSizedCT.lean`, which only this module imported.
section

/-! # Domain checking branches only on the public shape -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Generate.checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.checkSized
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have CT := RelCT.seq (generateParameters_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩))
      (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingOperationWith_agrees {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (checkingParams s).p = (checkingParams t).p)
    (Q : (checkingParams s).q = (checkingParams t).q)
    (sized : Nat → Nat → Prog isa)
    (sizedCT : RelCT isa (fun u v =>
      Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s u ∧
      Installed (argumentPointer t 4) ((arg t 5).toNat*8) Generate.checkArguments 0 2 3 t v)
      (sized (arg s 2).toNat (arg s 3).toNat) (VG.X86.Taint.Agree (workspaceTaint false)))
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.checkParametersWith sized) s tr sf) (F : Exec isa (Generate.checkParametersWith sized) t ur tf) : tr = ur := by
  let L := checkingLayout s A
  have LayoutEq := checkingLayout_eq A B args SP P Q
  have Size := args 5 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 4 (by decide))
  have PL := args 2 (by decide)
  have QL := args 3 (by decide)
  have DL := args 2 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s u ∧
    Installed (argumentPointer t 4) ((arg t 5).toNat * 8) Generate.checkArguments 0 2 3 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, checkingLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, checkingLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (2, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, checkingLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (3, .qLen) (by decide))
  have Sized := sizedCT
  have Dispatch := generationDispatch_relCT sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Generate.checkEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Generate.checkEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 4 Generate.checkArguments _ _ _ _ _ _
        ⟨SP, args 4 (by decide), (A.stackArgument (by decide : 4 < 6)).readSrc,
          (B.stackArgument (by decide : 4 < 6)).readSrc⟩ E1 F1
      have I := wp_result (checkingEntry_ok A) E1
      have J := wp_result (checkingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]


theorem checkingOperation_agrees {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (checkingParams s).p = (checkingParams t).p)
    (Q : (checkingParams s).q = (checkingParams t).q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.checkParameters) s tr sf) (F : Exec isa (Generate.checkParameters) t ur tf) : tr = ur := by
  let L := checkingLayout s A
  have LayoutEq := checkingLayout_eq A B args SP P Q
  have DL := args 2 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s u ∧
    Installed (argumentPointer t 4) ((arg t 5).toNat * 8) Generate.checkArguments 0 2 3 t v
  have Sized : RelCT isa R (Generate.checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (checkingSized_relCT L (arg s 2).toNat (by simp [L, checkingLayout, checkingInputs])
      (by simp [L, checkingLayout, checkingInputs]) (by simp [L, checkingLayout, checkingInputs])
      (checkingInputs_shape _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨checkingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using checkingInstalled_ready B H.2
  exact checkingOperationWith_agrees A B args SP P Q Generate.checkSized Sized E F

end VG.Proof.Dsa.X86
