module

public import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivate
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.LayoutAgreement
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
public import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- separate module: the constant-time proof costs more than its imports, and the contract
-- module's satisfiability witness should not re-check it.

/-! # i686 private-key validation traces from public arguments

The validator branches only on the public widths and the shape of the
public domain. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def privateValidatingInputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen),
    (.input .x, qLen), (.input .nonce, qLen)]

def privateValidatingPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 0
  | .input .q => arg s 0 + arg s 2
  | .input .g => arg s 0 + arg s 2 + arg s 3
  | .input .y => arg s 0 + arg s 2 + arg s 3 + arg s 2
  | .input .x => arg s 0 + arg s 2 + arg s 3 + arg s 2 + arg s 2
  | .input .nonce => arg s 0 + arg s 2 + arg s 3 + arg s 2 + arg s 2
  | _ => 0

def privateValidatingKey (s : State) : Spec.Dsa.Key :=
  Spec.Dsa.publicKeyBytes (arg s 2).toNat (arg s 3).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)

/-- The checker's entry stores p_len as the digest length (`checkArguments`),
so the shape checks' digest prefix is computed from it. -/
def privateValidatingLayout (s : State) (A : PrivateValidatingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 4
  size := (arg s 5).toNat * 8
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  p := (privateValidatingKey s).params.p
  q := (privateValidatingKey s).params.q
  widths := A.lengths
  extent := A.used
  inputs := privateValidatingInputs (arg s 2).toNat (arg s 3).toNat
  pointers := privateValidatingPointers s
  stable := by
    intro input hi
    simp only [privateValidatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 2).toNat (Spec.Dsa.bitLength (privateValidatingKey s).params.q / 8)

theorem privateValidatingInputs_shape (pLen qLen : Nat) :
    ∀ input ∈ privateValidatingInputs pLen qLen, ShapePointer input.1 := by
  intro input hi
  simp only [privateValidatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem privateValidatingInstalled_ready {s t : State} (A : PrivateValidatingABI s) (I : PrivateInstalled s t) :
    ShapeCallReady (privateValidatingLayout s A) (arg s 2).toNat t := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, Bytes⟩ := I.installed.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.installed.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, Value⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr Yptr Xptr
  have Value' : Spec.Dsa.publicKeyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) =
      ⟨⟨operandValue t (argumentPointer s 4) (.input .p) (arg s 2).toNat,
        operandValue t (argumentPointer s 4) (.input .q) (arg s 3).toNat,
        operandValue t (argumentPointer s 4) (.input .g) (arg s 2).toNat⟩,
        operandValue t (argumentPointer s 4) (.input .y) (arg s 2).toNat, none⟩ := by
    obtain ⟨_, _, _, _, V⟩ := publicKey_buffers Key L.1 L.2 (by have := A.keyLength; omega) Bytes Qptr Gptr Yptr
    rw [← V, ← Bytes]
  refine ⟨I.installed.keeps.1 .esp (by decide), I.installed.scr, ?_, ?_, ?_, ?_,
    congrArg BitVec.toNat (I.installed.arguments (2, .digestLen) (by decide))⟩
  · intro input hi
    simp only [privateValidatingLayout, privateValidatingInputs, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact Y
    · exact X
    · exact X.retarget I.nonce
  · intro input hi
    simp only [privateValidatingLayout, privateValidatingInputs, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact I.installed.arguments (0, .p) (by decide)
    · exact I.installed.qPointer
    · exact I.installed.gPointer
    · exact I.installed.yPointer
    · exact I.installed.xPointer
    · exact I.nonce.trans I.installed.xPointer
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.p) Value').symm
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.q) Value').symm

theorem privateValidatingLayout_eq {s t : State} (A : PrivateValidatingABI s) (B : PrivateValidatingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (privateValidatingKey s).params.p = (privateValidatingKey t).params.p)
    (Q : (privateValidatingKey s).params.q = (privateValidatingKey t).params.q) :
    privateValidatingLayout s A = privateValidatingLayout t B := by
  have A0 := args 0 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have pointers : privateValidatingPointers s = privateValidatingPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [privateValidatingPointers, A0, A2, A3]
    | «local» d => rfl
    | signatureS => rfl
  simp only [privateValidatingLayout, SP, argumentPointer, A2, A3, A4, A5, P, Q, pointers]

theorem privateValidatingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Generate.checkSizedWith PrevalidatedSign.validateCompute L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.checkSizedWith
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have Pc : CallOperand L (.input .p) L.pLen := .inl ⟨_, P, Nat.le_refl _⟩
    have Qc : CallOperand L (.input .q) L.qLen := .inl ⟨_, Q, Nat.le_refl _⟩
    have Gc : CallOperand L (.input .g) L.pLen := .inl ⟨_, G, Nat.le_refl _⟩
    have Yc : CallOperand L (.input .y) L.pLen := .inl ⟨_, Y, Nat.le_refl _⟩
    have Xc : CallOperand L (.input .x) L.qLen := .inl ⟨_, X, Nat.le_refl _⟩
    have Kc : CallOperand L (.input .nonce) L.qLen := .inl ⟨_, K, Nat.le_refl _⟩
    have CT := RelCT.seq (RelCT.seq (callPublicKey_relCT L Pc Qc Gc Yc)
      (callPrivateKey_relCT L Pc Qc Gc Yc Xc Kc))
      (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

theorem validateEntry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 4 = stackValue t 4 ∧
      readSrc s (.mem (Entry.argument 4)) = some (stackValue s 4) ∧
      readSrc t (.mem (Entry.argument 4)) = some (stackValue t 4))
      (.block PrevalidatedSign.validateEntry) (VG.X86.Taint.Agree entryTaint) :=
  RelCT.block_append (RelCT.seq (installEntry_relCT 4 Generate.checkArguments)
    (checkedBlockInvariant (τ' := entryTaint) rfl rfl))

theorem privateValidatingOperation_agrees {s t : State} (A : PrivateValidatingABI s) (B : PrivateValidatingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (privateValidatingKey s).params.p = (privateValidatingKey t).params.p)
    (Q : (privateValidatingKey s).params.q = (privateValidatingKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PrevalidatedSign.validate s tr sf) (F : Exec isa PrevalidatedSign.validate t ur tf) :
    tr = ur := by
  let L := privateValidatingLayout s A
  have LayoutEq := privateValidatingLayout_eq A B args SP P Q
  have Size := args 5 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 4 (by decide))
  have PL := args 2 (by decide)
  have QL := args 3 (by decide)
  have DL := args 2 (by decide)
  let R := fun u v => PrivateInstalled s u ∧ PrivateInstalled t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.installed.scr, ?_⟩
    simpa only [L, privateValidatingLayout, Base, Size] using H.2.installed.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.installed.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, privateValidatingLayout, Base, PL] using
      congrArg BitVec.toNat (H.2.installed.arguments (2, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.installed.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, privateValidatingLayout, Base, QL] using
      congrArg BitVec.toNat (H.2.installed.arguments (3, .qLen) (by decide))
  have Sized : RelCT isa R (Generate.checkSizedWith PrevalidatedSign.validateCompute L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (privateValidatingSized_relCT L (arg s 2).toNat
      (by simp [L, privateValidatingLayout, privateValidatingInputs])
      (by simp [L, privateValidatingLayout, privateValidatingInputs])
      (by simp [L, privateValidatingLayout, privateValidatingInputs])
      (by simp [L, privateValidatingLayout, privateValidatingInputs])
      (by simp [L, privateValidatingLayout, privateValidatingInputs])
      (by simp [L, privateValidatingLayout, privateValidatingInputs])
      (privateValidatingInputs_shape _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨privateValidatingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using privateValidatingInstalled_ready B H.2
  have Dispatch := generationDispatch_relCT (Generate.checkSizedWith PrevalidatedSign.validateCompute)
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block PrevalidatedSign.validateEntry)
    (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block PrevalidatedSign.validateEntry)
    (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := validateEntry_relCT _ _ _ _ _ _
        ⟨SP, args 4 (by decide), (A.stackArgument (by decide : 4 < 6)).readSrc,
          (B.stackArgument (by decide : 4 < 6)).readSrc⟩ E1 F1
      have I := wp_result (privateValidatingEntry_ok A) E1
      have J := wp_result (privateValidatingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86
