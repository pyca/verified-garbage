module

public import VerifiedGarbage.Proof.Dsa.X86.PointerTiming

/-! # Constant-time release of internal arithmetic results -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreStore_workspace_relCT (n len output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block (Core.store n len output)) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.store Core.pointer
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq (checkedProgramChange (σ := workspaceTaint true) (τ' := { workspaceTaint true with flags := true })
    (hint := .block []) ?_ rfl) ?_
  · change taint.checkBlock (workspaceTaint false) [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 output))] = _
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change taint.checkBlock (workspaceTaint false) [.mov .esi (.reg .edi), .alu .add .esi (.imm 0)] = _
    rfl
  · apply RelCT.block_append
    apply RelCT.seq (checkedBlockInvariant (τ' := { workspaceTaint true with regs := .ofList [.edi, .esi, .ecx] }) ?_ rfl)
      (storeComponent_relCT len n (slot n 6))
    rfl

theorem coreStore_relCT (n len output : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size)
      (.block (Core.store n len output)) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.store
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq ((pointer_relCT (.local output) base size hz).mono ?_ (fun _ _ h => h)) ?_
  · intro s t ⟨S, T⟩
    refine ⟨S, T, ?_⟩
    have G : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
    change s.gpr .edi + BitVec.ofNat 32 output = t.gpr .edi + BitVec.ofNat 32 output
    rw [G]
  · apply RelCT.block_append
    apply RelCT.seq (checkedBlockInvariant (τ' := { workspaceTaint true with regs := .ofList [.edi, .esi, .ecx] }) ?_ rfl)
      (storeComponent_relCT len n (slot n 6))
    rfl

end VG.Proof.Dsa.X86
