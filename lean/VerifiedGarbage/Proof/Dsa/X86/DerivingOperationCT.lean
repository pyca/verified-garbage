module

public import VerifiedGarbage.Proof.Dsa.X86.DerivingLayout
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.DerivingEntry
import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.DeriveFailureTiming
/-! # Whole domain-deriving traces from common public arguments and domain values -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/DeriveBodyTiming.lean`, which only this module imported.
section

/-! # Exponentiation and output copies preserve the public layout -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    RelCT isa (fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t)
      (.seq (Generate.deriveCompute L.pLen L.qLen) (Generate.writeKey L.pLen L.qLen))
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) := by
  have W := L.lengths
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t) ?_ ?_
  · intro s t tr ur sf tf ⟨Pair, S, T⟩ E F
    obtain ⟨Trace, Pair'⟩ := deriveCompute_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, X, Nat.le_refl _⟩)
      _ _ _ _ _ _ Pair E F
    have Es := (wp_result (deriveCompute_ok Pair.1.moduli (Pair.1.buffers _ G) (Pair.1.buffers _ X) rfl rfl) E).2.2.2
    have Et := (wp_result (deriveCompute_ok Pair.2.moduli (Pair.2.buffers _ G) (Pair.2.buffers _ X) rfl rfl) F).2.2.2
    exact ⟨Trace, Pair', S.keep Es, T.keep Et⟩
  · apply (writeKey_relCT L.base L.size L.pLen L.qLen out L.saved ho (by omega) A).mono ?_ (fun _ _ h => h)
    intro s t ⟨Pair, S, T⟩
    exact ⟨S.writeReady Pair.1 Params X A, T.writeReady Pair.2 Params X A,
      Pair.pointer (.inl ⟨_, P, Nat.le_refl _⟩), Pair.pointer (.inl ⟨_, X, Nat.le_refl _⟩)⟩

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/DeriveSizedTiming.lean`, which only this module imported.
section

/-! # Derivation branches only on the public domain shape -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveSized_relCT (L : CallLayout) (out : BitVec 32) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8))
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      KeyOutputReady L out s ∧ KeyOutputReady L out t)
      (Generate.deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => (shapeValid L.p L.q → CallPair L s t) ∧
    Scr s L.base L.size ∧ Scr t L.base L.size ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t
  unfold Generate.deriveSized
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf = some (!decide (shapeValid L.p L.q)) ∧
      t.zf = some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S, T, Os, Ot⟩ E F
    have Trace := (shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S, T⟩ E F).1
    obtain ⟨Zs, Ms, Ks, Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt, Mt, Kt, Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    exact ⟨Trace, ⟨fun h => ⟨(Ms h).ready, (Mt h).ready⟩,
      S.scr.of_keeps Ks (by decide), T.scr.of_keeps Kt (by decide), Os.shape Fs Ks, Ot.shape Ft Kt⟩, Zs, Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (deriveBody_relCT L out P Q G X Params ho A).mono
        (fun _ _ H => ⟨H.1 valid, H.2.2.2⟩) (fun _ _ h => h)
    · simp only [valid, decide_false, Bool.not_false, ite_true]
      exact (deriveFailure_relCT L.pLen L.qLen L.base L.size L.saved).mono
        (fun _ _ H => ⟨H.2.1, H.2.2.1, H.2.2.2.1.pointer.trans H.2.2.2.2.pointer.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingOperationWith_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q)
    (sized : Nat → Nat → Prog isa) (Is It : Mem → Prop)
    (Cs : Is s.mem) (Ct : It t.mem)
    (stableS : ∀ {a b}, Outside (argumentPointer s 7) 0 8272 a b → Is a → Is b)
    (stableT : ∀ {a b}, Outside (argumentPointer t 7) 0 8272 a b → It a → It b)
    (sizedCT : RelCT isa (fun u v =>
      Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s u ∧
      Installed (argumentPointer t 7) ((arg t 8).toNat*8) Generate.deriveArguments 2 4 6 t v ∧
      Is u.mem ∧ It v.mem)
      (sized (arg s 4).toNat (arg s 6).toNat) (VG.X86.Taint.Agree (workspaceTaint false)))
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.deriveKeyWith sized) s tr sf) (F : Exec isa (Generate.deriveKeyWith sized) t ur tf) : tr = ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have Size := args 8 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 7 (by decide))
  have PL := args 4 (by decide)
  have QL := args 6 (by decide)
  have DL := args 4 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s u ∧
    Installed (argumentPointer t 7) ((arg t 8).toNat * 8) Generate.deriveArguments 2 4 6 t v ∧ Is u.mem ∧ It v.mem
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.1.compare K2 O2, by rw [O1]; exact H.2.2.1, by rw [O2]; exact H.2.2.2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, derivingLayout, Base, Size] using H.2.1.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (4, .pLen) (by decide)), ?_⟩
    simpa only [L, derivingLayout, Base, PL] using congrArg BitVec.toNat (H.2.1.arguments (4, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (6, .qLen) (by decide)), ?_⟩
    simpa only [L, derivingLayout, Base, QL] using congrArg BitVec.toNat (H.2.1.arguments (6, .qLen) (by decide))
  have Sized := sizedCT
  have Dispatch := generationDispatch_relCT sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Generate.deriveEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Generate.deriveEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 7 Generate.deriveArguments _ _ _ _ _ _
        ⟨SP, args 7 (by decide), (A.stackArgument (by decide : 7 < 9)).readSrc,
          (B.stackArgument (by decide : 7 < 9)).readSrc⟩ E1 F1
      obtain ⟨I,Oi⟩ := wp_result (derivingEntry_precise A) E1
      obtain ⟨J,Oj⟩ := wp_result (derivingEntry_precise B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J,stableS Oi Cs,stableT Oj Ct⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]


theorem derivingOperation_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.deriveKey) s tr sf) (F : Exec isa (Generate.deriveKey) t ur tf) : tr = ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have DL := args 4 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s u ∧
    Installed (argumentPointer t 7) ((arg t 8).toNat*8) Generate.deriveArguments 2 4 6 t v
  have Sized : RelCT isa R (Generate.deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (deriveSized_relCT L (arg s 0) (arg s 4).toNat
      (by simp [L, derivingLayout, derivingInputs]) (by simp [L, derivingLayout, derivingInputs])
      (by simp [L, derivingLayout, derivingInputs]) (by simp [L, derivingLayout, derivingInputs])
      (by simp [L, derivingLayout, derivingInputs]) (derivingInputs_shape _ _) rfl
      (by change (arg s 0).toNat + (3 * (arg s 4).toNat + 2 * (arg s 6).toNat) ≤ _
          rw [← A.outLength]; exact A.outBound)
      (by change Region.Disjoint _ ⟨argumentPointer s 0, 3 * (arg s 4).toNat + 2 * (arg s 6).toNat⟩
          rw [← A.outLength]; exact A.outScratch.symm)).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨derivingInstalled_ready A H.1, ?_, derivingInstalled_output A H.1, ?_⟩
    · simpa only [L, LayoutEq, DL] using derivingInstalled_ready B H.2
    · simpa only [L, LayoutEq, args 0 (by decide)] using derivingInstalled_output B H.2
  exact derivingOperationWith_agrees A B args SP P Q Generate.deriveSized (fun _ => True)
    (fun _ => True) trivial trivial (fun _ _ => trivial) (fun _ _ => trivial)
    (Sized.mono (fun _ _ H => ⟨H.1,H.2.1⟩) (fun _ _ h => h)) E F

end VG.Proof.Dsa.X86
