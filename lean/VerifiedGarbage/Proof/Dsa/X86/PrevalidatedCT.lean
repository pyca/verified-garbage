module

public import VerifiedGarbage.Proof.Dsa.X86.Validating
public import VerifiedGarbage.Proof.Dsa.X86.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86.VerifyLayout
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.LayoutAgreement
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifyTiming
import VerifiedGarbage.Proof.Dsa.X86.CallMinusTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.OutputBytes

-- separate module: the constant-time proofs cost more than their imports, and the contract
-- module's satisfiability witnesses should not re-check them.

/-! # Whole i686 validation and prevalidated verification traces from public arguments

Both branch only on the public widths and the shape of the public domain. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem prevalidatedSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (R : (.input .signature, L.qLen) ∈ L.inputs) (S : (.signatureS, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Prevalidated.sized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Prevalidated.sized
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have W := L.lengths
    have Pc : CallOperand L (.input .p) L.pLen := .inl ⟨_, P, Nat.le_refl _⟩
    have Qc : CallOperand L (.input .q) L.qLen := .inl ⟨_, Q, Nat.le_refl _⟩
    have Gc : CallOperand L (.input .g) L.pLen := .inl ⟨_, G, Nat.le_refl _⟩
    have Yc : CallOperand L (.input .y) L.pLen := .inl ⟨_, Y, Nat.le_refl _⟩
    have Rc : CallOperand L (.input .signature) L.qLen := .inl ⟨_, R, Nat.le_refl _⟩
    have Sc : CallOperand L .signatureS L.qLen := .inl ⟨_, S, Nat.le_refl _⟩
    have Dc : CallOperand L (.input .digest) L.digestPrefix :=
      .inl ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩
    have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega)
    have Compute : RelCT isa (CallPair L) (Prevalidated.compute L.pLen L.qLen) (CallPair L) := by
      unfold Prevalidated.compute Core.sequence
      dsimp only [List.foldr]
      exact RelCT.seq (callMinusQ_relCT L qMinusTwo Qc (by decide) (by change 14912 + L.qLen ≤ 15712; omega))
        (RelCT.seq (RelCT.seq
          (callRange_relCT L L.qLen .q (.input .signature) false Qc Rc (by omega) (by omega) L.aligned.2)
          (callRange_relCT L L.qLen .q .signatureS false Qc Sc (by omega) (by omega) L.aligned.2))
        (RelCT.seq (callVerify_relCT L Pc Qc Gc Yc Rc Sc Dc (by rw [hd]; omega))
        (RelCT.seq (callEqual_relCT L L.qLen (.local u) (.input .signature) U Rc (by omega) (by omega)
          L.aligned.2)
        (RelCT.block_nil (fun _ _ h => h)))))
    have CT := RelCT.seq Compute (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

theorem prevalidatedOperation_agrees {s t : State} (A : VerifyingABI s) (B : VerifyingABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (verifyKey s).params.p = (verifyKey t).params.p)
    (Q : (verifyKey s).params.q = (verifyKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa Prevalidated.verify s tr sf) (F : Exec isa Prevalidated.verify t ur tf) : tr = ur := by
  let L := verifyLayout s A
  have LayoutEq := verifyLayout_eq A B args SP P Q
  have Size := args 9 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 8 (by decide))
  have PL := args 2 (by decide)
  have QL := args 3 (by decide)
  have DL := args 7 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s u ∧
    Installed (argumentPointer t 8) ((arg t 9).toNat * 8) Entry.verifyArguments 0 2 3 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, verifyLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, verifyLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (2, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, verifyLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (3, .qLen) (by decide))
  have Sized : RelCT isa R (Prevalidated.sized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (prevalidatedSized_relCT L (arg s 7).toNat (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (verifyInputs_shape _ _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨verifyingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using verifyingInstalled_ready B H.2
  have Dispatch := generationDispatch_relCT Prevalidated.sized
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Entry.verifyEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Entry.verifyEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 8 Entry.verifyArguments _ _ _ _ _ _
        ⟨SP, args 8 (by decide), (A.stackArgument (by decide : 8 < 10)).readSrc,
          (B.stackArgument (by decide : 8 < 10)).readSrc⟩ E1 F1
      have I := wp_result (verifyingEntry_ok A) E1
      have J := wp_result (verifyingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

def validatingInputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen)]

def validatingPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 0
  | .input .q => arg s 0 + arg s 2
  | .input .g => arg s 0 + arg s 2 + arg s 3
  | .input .y => arg s 0 + arg s 2 + arg s 3 + arg s 2
  | _ => 0

def validatingKey (s : State) : Spec.Dsa.Key := Spec.Dsa.publicKeyBytes (arg s 2).toNat (arg s 3).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)

/-- The checker's entry stores p_len as the digest length (`checkArguments`),
so the shape checks' digest prefix is computed from it. -/
def validatingLayout (s : State) (A : ValidatingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 4
  size := (arg s 5).toNat * 8
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  p := (validatingKey s).params.p
  q := (validatingKey s).params.q
  widths := A.lengths
  extent := A.used
  inputs := validatingInputs (arg s 2).toNat (arg s 3).toNat
  pointers := validatingPointers s
  stable := by
    intro input hi
    simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 2).toNat (Spec.Dsa.bitLength (validatingKey s).params.q / 8)

theorem validatingInputs_shape (pLen qLen : Nat) :
    ∀ input ∈ validatingInputs pLen qLen, ShapePointer input.1 := by
  intro input hi
  simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem validatingInstalled_ready {s t : State} (A : ValidatingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t) :
    ShapeCallReady (validatingLayout s A) (arg s 2).toNat t := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, Yptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, Value⟩ := publicKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr Yptr
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_,
    congrArg BitVec.toNat (I.arguments (2, .digestLen) (by decide))⟩
  · intro input hi
    simp only [validatingLayout, validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact Y
  · intro input hi
    simp only [validatingLayout, validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact I.arguments (0, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
    · exact I.yPointer
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.p) Value).symm
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.q) Value).symm

theorem validatingLayout_eq {s t : State} (A : ValidatingABI s) (B : ValidatingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (validatingKey s).params.p = (validatingKey t).params.p)
    (Q : (validatingKey s).params.q = (validatingKey t).params.q) :
    validatingLayout s A = validatingLayout t B := by
  have A0 := args 0 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have pointers : validatingPointers s = validatingPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [validatingPointers, A0, A2, A3]
    | «local» d => rfl
    | signatureS => rfl
  simp only [validatingLayout, SP, argumentPointer, A2, A3, A4, A5, P, Q, pointers]

theorem validatingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Generate.checkSizedWith Validate.publicKey L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.checkSizedWith
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have CT := RelCT.seq (callPublicKey_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, Y, Nat.le_refl _⟩))
      (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

theorem validatingOperation_agrees {s t : State} (A : ValidatingABI s) (B : ValidatingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (validatingKey s).params.p = (validatingKey t).params.p)
    (Q : (validatingKey s).params.q = (validatingKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa Prevalidated.validate s tr sf) (F : Exec isa Prevalidated.validate t ur tf) : tr = ur := by
  let L := validatingLayout s A
  have LayoutEq := validatingLayout_eq A B args SP P Q
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
    simpa only [L, validatingLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, validatingLayout, Base, PL] using
      congrArg BitVec.toNat (H.2.arguments (2, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, validatingLayout, Base, QL] using
      congrArg BitVec.toNat (H.2.arguments (3, .qLen) (by decide))
  have Sized : RelCT isa R (Generate.checkSizedWith Validate.publicKey L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (validatingSized_relCT L (arg s 2).toNat (by simp [L, validatingLayout, validatingInputs])
      (by simp [L, validatingLayout, validatingInputs]) (by simp [L, validatingLayout, validatingInputs])
      (by simp [L, validatingLayout, validatingInputs]) (validatingInputs_shape _ _) rfl).mono ?_
      (fun _ _ h => h)
    intro u v H
    refine ⟨validatingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using validatingInstalled_ready B H.2
  have Dispatch := generationDispatch_relCT (Generate.checkSizedWith Validate.publicKey)
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
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
      have I := wp_result (validatingEntry_ok A) E1
      have J := wp_result (validatingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86
