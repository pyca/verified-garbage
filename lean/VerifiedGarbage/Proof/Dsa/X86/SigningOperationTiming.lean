module

public import VerifiedGarbage.Proof.Dsa.X86.LayoutAgreement
public import VerifiedGarbage.Proof.Dsa.X86.SignSizedTiming
public import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
public import VerifiedGarbage.Proof.Dsa.X86.SigningOperation

/-! # Whole signing traces from common public arguments and domain values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingOperation_agrees {s t : State} (A : SigningABI s) (B : SigningABI t)
    (args : ∀ i < 11, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (signKey s).params.p = (signKey t).params.p)
    (Q : (signKey s).params.q = (signKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Entry.operation true) s tr sf) (F : Exec isa (Entry.operation true) t ur tf) : tr = ur := by
  let L := signLayout s A
  have LayoutEq := signLayout_eq A B args P Q
  have Size := args 10 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 9 (by decide))
  have PL := args 4 (by decide)
  have QL := args 6 (by decide)
  have DL := args 8 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s u ∧
    Installed (argumentPointer t 9) ((arg t 10).toNat * 8) Entry.signArguments 2 4 6 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, signLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (4, .pLen) (by decide)), ?_⟩
    simpa only [L, signLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (4, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (6, .qLen) (by decide)), ?_⟩
    simpa only [L, signLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (6, .qLen) (by decide))
  have Sized : RelCT isa R (Entry.sized true L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (signSized_relCT L (arg s 8).toNat (arg s 0) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (signInputs_shape _ _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨⟨signingInstalled_ready A H.1, ?_⟩, signingInstalled_output A H.1, ?_⟩
    · simpa only [L, LayoutEq, DL] using signingInstalled_ready B H.2
    · simpa only [L, LayoutEq, args 0 (by decide)] using signingInstalled_output B H.2
  have Dispatch := widthDispatch_relCT true [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Entry.signEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Entry.signEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 9 Entry.signArguments _ _ _ _ _ _
        ⟨SP, args 9 (by decide), (A.stackArgument (by decide : 9 < 11)).readSrc,
          (B.stackArgument (by decide : 9 < 11)).readSrc⟩ E1 F1
      have I := wp_result (signingEntry_ok A) E1
      have J := wp_result (signingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86
