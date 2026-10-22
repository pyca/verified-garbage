module
public import VerifiedGarbage.Impl.Dsa.X86.Core
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Constant-time release of internal arithmetic results -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreStoreAt_workspace_relCT (len input output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (Core.storeAt len input output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.storeAt Core.pointer
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_
    (storeComponent_relCT len input)
  apply checkedProgramChange (σ := workspaceTaint true) (τ' := { regs := .ofList [.edi, .esi, .ecx], flags := true })
    (hint := .block []) ?_ rfl
  change taint.checkBlock (workspaceTaint false)
    [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 output)), .mov .ecx (.imm (BitVec.allOnes 32))] = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
  change taint.checkBlock (workspaceTaint false) [.mov .esi (.reg .edi), .alu .add .esi (.imm 0), .mov .ecx (.imm 0)] = _
  rfl

theorem coreStore_workspace_relCT (len output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (Core.store len output) (VG.X86.Taint.Agree (workspaceTaint true)) := coreStoreAt_workspace_relCT len (slot ((len + 7) / 8) 6) output

end VG.Proof.Dsa.X86
