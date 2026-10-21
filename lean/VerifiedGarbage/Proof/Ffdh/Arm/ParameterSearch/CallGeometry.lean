module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! The candidate's 184 bytes and its 24 argument bytes lie below the search frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem callStack_fits {sp : BitVec 32} (fit : 208 ≤ sp.toNat) : 184 ≤ (sp - 24#32).toNat := by
  rw [FrameStack.sub_toNat' (by omega : 24 ≤ sp.toNat)]
  omega

theorem callArguments_fits {sp : BitVec 32} (fit : 208 ≤ sp.toNat) : (sp - 24#32).toNat + 24 ≤ 2 ^ 32 := by
  rw [FrameStack.sub_toNat' (by omega : 24 ≤ sp.toNat)]
  have := sp.isLt
  omega

theorem callArguments_sub {sp : BitVec 32} (fit : 208 ≤ sp.toNat) :
    (⟨State.addr (sp - 24#32), 24⟩ : Region).Sub (FrameStack.belowA sp 208) :=
  FrameStack.belowA_sub (by decide) fit

theorem callStack_sub {sp : BitVec 32} (fit : 208 ≤ sp.toNat) :
    (FrameStack.belowA (sp - 24#32) 184).Sub (FrameStack.belowA sp 208) :=
  FrameStack.belowA_inner (by decide) fit

theorem callStack_arguments_separate {sp : BitVec 32} (fit : 208 ≤ sp.toNat) :
    (FrameStack.belowA (sp - 24#32) 184).Disjoint ⟨State.addr (sp - 24#32), 20⟩ := by
  rw [FrameStack.belowA, FrameStack.addr_sub' (callStack_fits fit)]
  exact (VG.Offset.base_disjoint_below _ (by decide)).symm

end VG.Proof.Ffdh.Arm.ParameterSearch
