module
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Public address schedules for the CRT workspace helpers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem copy_public (n o a : Nat) : KeyPublic (copy n o a) := by
  let reference : Prog isa := copy 1 0 1
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp, .edx, .ecx], flags := true }
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (copy n o a) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem eqS_public (n d a b t : Nat) : KeyPublic (eqS n d a b t) := by
  let reference : Prog isa := eqS 1 100 0 1 2
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp, .edx], flags := false }
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (eqS n d a b t) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem orOne_public (n j : Nat) : KeyPublic (.block (orOne n j)) := by
  let reference : Prog isa := .block (orOne 1 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := workspaceTaint true
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (orOne n j)) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem clrLow_public (n j : Nat) : KeyPublic (.block (clrLow n j)) := by
  let reference : Prog isa := .block (clrLow 1 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := workspaceTaint true
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (clrLow n j)) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem setOnes_public (n i j : Nat) : KeyPublic (.block (setOne n i ++ setOne n j)) := by
  let reference : Prog isa := .block (setOne 1 0 ++ setOne 1 1)
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .eax], flags := false }
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (setOne n i ++ setOne n j)) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem andSlots_public (a b c d e f g h i : Nat) : KeyPublic (.block (andS a b c ++ andS d e f ++ andS g h i)) := by
  let reference : Prog isa := .block (andS 100 104 108 ++ andS 112 116 120 ++ andS 124 128 132)
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := workspaceTaint true
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (andS a b c ++ andS d e f ++ andS g h i)) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem division_public (n q r d t : Nat) : KeyPublic (VG.Impl.Rsa.X86.Div.code n q r d t) := by
  let reference : Prog isa := VG.Impl.Rsa.X86.Div.code 1 0 0 0 0
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp, .edx], flags := true }
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.code n q r d t) reference (workspaceTaint true) hint (by rfl) (by rfl) (by decide +kernel)).trans (by rfl)
  · decide +kernel

end VG.Proof.Rsa.X86.Keys
