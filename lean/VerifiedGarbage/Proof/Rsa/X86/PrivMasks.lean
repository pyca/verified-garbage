module
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Rsa.X86.PrivStatusMask
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest

/-! # Complete branchless private-result release decision -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Dsa.X86

theorem masks_ok (s : State) (accepted equal : Bool)
    (good : s.gpr .ebx = BitVec.ofNat 32 accepted.toNat)
    (eq : (s.gpr .ebp = 0) ↔ equal = true) :
    WP isa (.block masks) s fun t =>
      t.gpr .edx = -BitVec.ofNat 32 (accepted && equal).toNat ∧
      t.gpr .ebx = (if accepted then if equal then 1 else 2 else 0) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp, .ebx] s t := by
  unfold masks
  refine WP.block_append (WP.mono (zeroTest_ok s) fun u ⟨E, M, K⟩ => ?_)
  have Eu : u.gpr .eax = BitVec.ofNat 32 equal.toNat := by
    rw [E]
    simp only [eq, Bool.decide_eq_true]
  refine WP.mono (statusMask_ok u accepted equal (by rw [K.1 .ebx (by decide), good]) Eu)
    fun t ⟨D, B, Mt, Kt⟩ => ?_
  exact ⟨D, B, Mt.trans M, (K.mono (by decide)).trans (Kt.mono (by decide))⟩

theorem masks_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block masks)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

end VG.Proof.Rsa.X86.PrivChecked
