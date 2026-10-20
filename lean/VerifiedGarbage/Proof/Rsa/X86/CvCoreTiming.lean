module
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming

import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.Rsa.X86.DivTiming
import VerifiedGarbage.Proof.Rsa.X86.InverseTiming
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # CRT division, binary inversion, and acceptance tests have a public schedule -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem firstDiv_public (w : Nat) : KeyPublic (firstDiv w) := by
  unfold firstDiv
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact copy_public ..
  · exact bitOf_public ..
  · exact division_public ..

theorem checks_public (w : Nat) : KeyPublic (checks w) := by
  unfold checks
  apply KeyPublic.seqs
  intro c hc
  simp only [invSetup, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact eqS_public .. | exact copy_public .. | exact orOne_public .. |
    exact setOnes_public .. | exact sub3_public .. | exact inverse_public .. |
    exact andSlots_public .. | exact clrLow_public ..

theorem divQ_public (w : Nat) : KeyPublic (divQ w) := by
  unfold divQ
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact copy_public ..
  · exact copy_public ..
  · exact clrLow_public ..
  · exact division_public ..

theorem core_public (w : Nat) : KeyPublic (core w) :=
  (firstDiv_public w).seq ((checks_public w).seq ((division_public ..).seq (divQ_public w)))

theorem core_constantTime (w : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (core w) := by
  let copyHint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (copy 1 0 1))
  let copyOut : VG.X86.Taint.T := { regs := .ofList [.edi, .ebp, .edx, .ecx], flags := true }
  have copyCheck : VG.Taint.check taint (workspaceTaint false) (copy w aDD aP) copyHint = some copyOut := by
    exact (check_of_erase_eq (copy w aDD aP) (copy 1 0 1) (workspaceTaint false) copyHint
      (by rfl) (by rfl) (by decide +kernel)).trans (by rfl)
  let bitHint := VG.Taint.hintOf taint (workspaceTaint false) (.block (bitOf 1 100 0))
  have bitCheck : VG.Taint.check taint (workspaceTaint false) (.block (bitOf w sPodd aP)) bitHint =
      some (workspaceTaint false) := by
    exact (check_of_erase_eq (.block (bitOf w sPodd aP)) (.block (bitOf 1 100 0))
      (workspaceTaint false) bitHint (by rfl) (by rfl) (by decide +kernel)).trans (by rfl)
  let divHint := VG.Proof.Rsa.X86.Div.divisionHint
  let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp, .edx], flags := true }
  have divCheck : VG.Taint.check taint (workspaceTaint false) (div w aDR) divHint = some out := by
    exact (check_of_erase_eq (div w aDR) (VG.Impl.Rsa.X86.Div.code 1 0 0 0 0)
      (workspaceTaint false) divHint (by rfl) (by rfl) (by decide +kernel)).trans (by rfl)
  let hint := VG.Taint.Hint.seq (workspaceTaint false) copyHint
    (.seq (workspaceTaint false) bitHint divHint)
  have first : VG.Taint.check taint (workspaceTaint false) (firstDiv w) hint = some out :=
    exponent_check_seq taint copyCheck (by decide +kernel)
      (exponent_check_seq taint bitCheck (by rfl) divCheck)
  obtain ⟨restHint, restOut, checked, _⟩ :=
    (checks_public w).seq ((division_public ..).seq (divQ_public w))
  have total : VG.Taint.check taint (workspaceTaint false) (core w)
      (.seq (workspaceTaint true) hint restHint) = some restOut :=
    exponent_check_seq taint first (by decide +kernel) checked
  exact VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (by rw [total]; rfl)

end VG.Proof.Rsa.X86.CrtValues
