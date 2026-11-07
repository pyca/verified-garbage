module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Mont.X86.Sparse
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.TCB.X86.State

/-! # Certified selection of the sparse P-256 reduction row -/

@[expose] public section

namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

theorem p256RedChoice_ok (n m : Nat) : (p256RedChoice n m).ok n m = true := by
  unfold p256RedChoice
  split
  next h => rcases h with ⟨rfl, rfl⟩; decide +kernel
  next _ => rfl

theorem p256RedEnabled_ok {M : Mod} {m : Nat} (h : M.ok m = true)
    (he : p256RedEnabled M = true) :
    M.n = 4 ∧ m = p256Prime ∧ minv32 M = 1 := by
  simp only [p256RedEnabled, Bool.and_eq_true, beq_iff_eq] at he
  have hr := M.ok_red h
  rw [he.1.2] at hr
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hr
  have hv := hr.1.2
  have hl := hr.1.1.2
  change (2 ^ 192 - 2 ^ 160 + 2 ^ 128 + 2 ^ 32) = (m + 1) / 2 ^ 64 at hv
  exact ⟨he.1.1, by unfold p256Prime; omega, he.2⟩

end VG.Proof.Mont.X86
