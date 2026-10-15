module

public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen

import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Component loads and masked stores have secret-independent traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem loadStep_relCT (len out j : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true))
      (.block (VG.Proof.Weierstrass.X86.ldStepL len out .esi j))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold VG.Proof.Weierstrass.X86.ldStepL
  split
  · apply checkedBlockInvariant (τ' := workspaceTaint true) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true) [.mov .eax (.mem (at_ .esi 0)), .bswap .eax, .store (sc 0) .eax] = _
    rfl
  · split
    · apply checkedBlockInvariant (τ' := workspaceTaint true) ?_ rfl
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
      change taint.checkBlock (workspaceTaint true) [.mov .eax (.mem (at_ .esi 0)), .bswap .eax, .shift .shr .eax (8 * (4 * (j + 1) - len)), .store (sc 0) .eax] = _
      rfl
    · apply checkedBlockInvariant (τ' := zeroTaint true) ?_ rfl
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
      change taint.checkBlock (workspaceTaint true) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
      rfl

theorem loadComponent_relCT (len n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (.block (loadComponent len n out))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold loadComponent
  rw [VG.Proof.Weierstrass.X86.loadBytes_eq]
  exact blockFlatMap_relCT _ _ (loadStep_relCT len out)

theorem storeByte_relCT (len j i : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true))
      (.block (([.mov .edx (.reg .eax)] : List Instr) ++
        (if len - 4 * j - 1 - i = 0 then [] else [.shift .shr .edx (8 * (len - 4 * j - 1 - i))]) ++
        ([.store8 (at_ .esi i) .dl] : List Instr))) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  split <;> apply checkedBlockInvariant (τ' := workspaceTaint true) ?_ rfl <;>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  · change taint.checkBlock (workspaceTaint true) [.mov .edx (.reg .eax), .store8 (at_ .esi 0) .dl] = _
    rfl
  · change taint.checkBlock (workspaceTaint true) [.mov .edx (.reg .eax), .shift .shr .edx (8 * (len - 4 * j - 1 - i)), .store8 (at_ .esi 0) .dl] = _
    rfl

theorem storeComponent_relCT (len n input : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (.block (storeComponent len n input))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold storeComponent VG.Impl.Weierstrass.X86.storeBytes
  apply blockFlatMap_relCT
  intro j
  split
  · apply checkedBlockInvariant (τ' := workspaceTaint true) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true) [.mov .eax (.mem (sc 0)), .alu .and .eax (.reg .ecx), .bswap .eax, .store (at_ .esi 0) .eax] = _
    rfl
  · split
    · apply RelCT.block_append
      apply RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint true) ?_ rfl)
      · apply blockFlatMap_relCT
        intro i
        simpa only [Nat.zero_add] using storeByte_relCT len j i
      · rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
        change taint.checkBlock (workspaceTaint true) [.mov .eax (.mem (sc 0)), .alu .and .eax (.reg .ecx)] = _
        rfl
    · exact RelCT.block_nil (fun _ _ h => h)

end VG.Proof.Dsa.X86
