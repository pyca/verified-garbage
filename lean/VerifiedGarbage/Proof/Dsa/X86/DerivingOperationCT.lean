module
public import VerifiedGarbage.Proof.Dsa.X86.DerivingLayout
import VerifiedGarbage.Proof.Dsa.X86.DerivingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation

import VerifiedGarbage.Proof.Dsa.X86.DeriveSizedTiming
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.DerivingEntry

/-! # Whole domain-deriving traces from common public arguments and domain values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingOperation_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.deriveKey) s tr sf) (F : Exec isa (Generate.deriveKey) t ur tf) : tr = ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have Size := args 8 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 7 (by decide))
  have PL := args 4 (by decide)
  have QL := args 6 (by decide)
  have DL := args 4 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s u ∧
    Installed (argumentPointer t 7) ((arg t 8).toNat * 8) Generate.deriveArguments 2 4 6 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, derivingLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (4, .pLen) (by decide)), ?_⟩
    simpa only [L, derivingLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (4, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (6, .qLen) (by decide)), ?_⟩
    simpa only [L, derivingLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (6, .qLen) (by decide))
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
  have Dispatch := deriveDispatch_relCT [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
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
      have I := wp_result (derivingEntry_ok A) E1
      have J := wp_result (derivingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86
