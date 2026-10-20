module
public import VerifiedGarbage.Proof.Dsa.X86.CheckingLayout
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation

import VerifiedGarbage.Proof.Dsa.X86.CheckingSizedCT
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.CheckingEntry

/-! # Whole domain-checking traces from common public arguments and domain values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingOperation_agrees {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (checkingParams s).p = (checkingParams t).p)
    (Q : (checkingParams s).q = (checkingParams t).q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.checkParameters) s tr sf) (F : Exec isa (Generate.checkParameters) t ur tf) : tr = ur := by
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
  have Sized : RelCT isa R (Generate.checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (checkingSized_relCT L (arg s 2).toNat (by simp [L, checkingLayout, checkingInputs])
      (by simp [L, checkingLayout, checkingInputs]) (by simp [L, checkingLayout, checkingInputs])
      (checkingInputs_shape _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨checkingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using checkingInstalled_ready B H.2
  have Dispatch := checkDispatch_relCT [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
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

end VG.Proof.Dsa.X86
