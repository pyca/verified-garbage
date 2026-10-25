module
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.KernelRfl


/-! # Public address schedules for the CRT workspace helpers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem copy_public (n o a : Nat) : KeyPublic (copy n o a) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (copy 1 0 1 : Prog isa))),
      ({ regs := .ofList [.edi, .esi, .ebp, .edx, .ecx], flags := true } : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (copy n o a) (copy 1 0 1 : Prog isa) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (copy 1 0 1 : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  · decide +kernel

theorem eqS_public (n d a b t : Nat) : KeyPublic (eqS n d a b t) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (eqS 1 100 0 1 2 : Prog isa))),
      ({ regs := .ofList [.edi, .esi, .ebp, .edx], flags := false } : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (eqS n d a b t) (eqS 1 100 0 1 2 : Prog isa) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (eqS 1 100 0 1 2 : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  · decide +kernel

theorem orOne_public (n j : Nat) : KeyPublic (.block (orOne n j)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (orOne 1 0) : Prog isa))),
      (workspaceTaint true : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (.block (orOne n j)) (.block (orOne 1 0) : Prog isa) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (orOne 1 0) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  · decide +kernel

theorem clrLow_public (n j : Nat) : KeyPublic (.block (clrLow n j)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (clrLow 1 0) : Prog isa))),
      (workspaceTaint true : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (.block (clrLow n j)) (.block (clrLow 1 0) : Prog isa) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (clrLow 1 0) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  · decide +kernel

theorem setOnes_public (n i j : Nat) : KeyPublic (.block (setOne n i ++ setOne n j)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (setOne 1 0 ++ setOne 1 1) : Prog isa))), ({ regs := .ofList [.edi, .esi, .eax], flags := false } : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (.block (setOne n i ++ setOne n j)) (.block (setOne 1 0 ++ setOne 1 1) : Prog isa) (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (setOne 1 0 ++ setOne 1 1) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  · decide +kernel

theorem andSlots_public (a b c d e f g h i : Nat) : KeyPublic (.block (andS a b c ++ andS d e f ++ andS g h i)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (andS 100 104 108 ++ andS 112 116 120 ++ andS 124 128 132) : Prog isa))), (workspaceTaint true : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (.block (andS a b c ++ andS d e f ++ andS g h i)) (.block (andS 100 104 108 ++ andS 112 116 120 ++ andS 124 128 132) : Prog isa) (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (andS 100 104 108 ++ andS 112 116 120 ++ andS 124 128 132) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  · decide +kernel

theorem division_public (n q r d t : Nat) : KeyPublic (VG.Impl.Rsa.X86.Div.code n q r d t) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.code 1 0 0 0 0 : Prog isa))), ({ regs := .ofList [.edi, .esi, .ebp, .edx], flags := true } : VG.X86.Taint.T), ?_, ?_⟩
  · exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.code n q r d t) (VG.Impl.Rsa.X86.Div.code 1 0 0 0 0 : Prog isa) (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.code 1 0 0 0 0 : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).trans (by kernel_rfl)
  · decide +kernel

end VG.Proof.Rsa.X86.Keys
