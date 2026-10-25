module

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Component loads and masked stores have secret-independent traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

/-- The workspace and the caller's buffer, with the cursor into it in `ebx`. -/
def cursorTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebx], flags := false }

theorem cursor_relCT (len : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true))
      (.block [.mov .ebx (.reg .esi), .alu .add .ebx (.imm (BitVec.ofNat 32 (len - 4)))])
      (VG.X86.Taint.Agree cursorTaint) :=
  erased_relCT _ (.block [.mov .ebx (.reg .esi), .alu .add .ebx (.imm 0)])
    (VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .ebx (.reg .esi), .alu .add .ebx (.imm 0)]))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem loadComponent_relCT (len n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (loadComponent len n out)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold loadComponent
  refine RelCT.seq (cursor_relCT len) (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_)
  · exact erased_relCT _ (VG.Impl.Mont.X86.Dynamic.wordLoop 1
        [.mov .eax (.mem (at_ .ebx 0)), .bswap .eax, .store (at_ .ebp 0) .eax, .alu .sub .ebx (.imm 4)])
      (VG.Taint.hintOf taint cursorTaint (Code.erase (VG.Impl.Mont.X86.Dynamic.wordLoop 1
        [.mov .eax (.mem (at_ .ebx 0)), .bswap .eax, .store (at_ .ebp 0) .eax, .alu .sub .ebx (.imm 4)])))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  · unfold zeroPad
    split
    · apply blockFlatMap_relCT
      intro j
      apply checkedBlockInvariant (τ' := zeroTaint true) ?_ rfl
      rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
      change taint.checkBlock (workspaceTaint true) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
      rfl
    · exact checkedProgramChange (zeros_check true _ _) rfl

theorem storeComponent_relCT (len input : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (storeComponent len input)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold storeComponent
  refine RelCT.seq (cursor_relCT len) ?_
  exact erased_relCT _ (VG.Impl.Mont.X86.Dynamic.wordLoop 1 [.mov .eax (.mem (at_ .ebp 0)),
      .alu .and .eax (.reg .ecx), .bswap .eax, .store (at_ .ebx 0) .eax, .alu .sub .ebx (.imm 4)])
    (VG.Taint.hintOf taint cursorTaint (Code.erase (VG.Impl.Mont.X86.Dynamic.wordLoop 1
      [.mov .eax (.mem (at_ .ebp 0)), .alu .and .eax (.reg .ecx), .bswap .eax, .store (at_ .ebx 0) .eax,
        .alu .sub .ebx (.imm 4)])))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.Dsa.X86
