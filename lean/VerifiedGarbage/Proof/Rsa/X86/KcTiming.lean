module

import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.Rsa.X86.MulModTiming
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Key-validation arithmetic uses public iteration counts and fixed addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem acc_public : KeyPublic (.block acc) :=
  ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem count_public (k : Nat) : KeyPublic (.block [.mov .esi (.imm (BitVec.ofNat 32 k))]) :=
  ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem one_public (w j : Nat) : KeyPublic (.block (setOne w j)) := by
  let reference : Prog isa := .block (setOne 1 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .eax], flags := false }
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (setOne w j)) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem crtChecks_public (w : Nat) : KeyPublic (crtChecks w) := by
  unfold crtChecks
  apply KeyPublic.seqs
  intro c hc
  simp only [eqA, ltA, mulA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  repeat' first | (rcases hc with hc | hc) | subst c
  all_goals first | exact eqS_public .. | exact acc_public | exact copy_public .. |
    exact clrLow_public .. | exact sub3_public .. | exact store_public _ |
    exact count_public _ | exact mulMod_public ..

theorem dChecks1_public (w : Nat) : KeyPublic (dChecks1 w) := by
  unfold dChecks1
  apply KeyPublic.seqs
  intro c hc
  simp only [ltA, divSet, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact sub3_public ..
  · exact store_public _
  · exact acc_public
  · exact copy_public ..
  · exact copy_public ..

theorem dChecks2_public (w : Nat) : KeyPublic (dChecks2 w) := by
  unfold dChecks2
  apply KeyPublic.seqs
  intro c hc
  simp only [eqA, divSet, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact eqS_public ..
  · exact acc_public
  · exact copy_public ..
  · exact copy_public ..

theorem dChecks3_public (w : Nat) : KeyPublic (dChecks3 w) :=
  (eqS_public ..).seq acc_public

end VG.Proof.Rsa.X86.KeyCheck
