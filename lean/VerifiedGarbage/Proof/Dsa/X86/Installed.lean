module
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Dsa.X86.SigningABI
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Weierstrass.PointContract

import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments

/-! # Installed argument records for the two cdecl entry points -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure Installed (base : Addr) (size : Nat) (args : List (Nat × Field))
    (keyArg pLenArg qLenArg : Nat) (s t : State) : Prop where
  scr : Scr t base size
  saved : Saved t.mem (off base) s.gpr Entry.savedRegisters
  arguments : ∀ a ∈ args, pointerValue base t (.input a.2) = arg s a.1
  qPointer : pointerValue base t (.input .q) = arg s keyArg + arg s pLenArg
  gPointer : pointerValue base t (.input .g) = arg s keyArg + arg s pLenArg + arg s qLenArg
  yPointer : pointerValue base t (.input .y) = arg s keyArg + arg s pLenArg + arg s qLenArg + arg s pLenArg
  xPointer : pointerValue base t (.input .x) = arg s keyArg + arg s pLenArg + arg s qLenArg + arg s pLenArg + arg s pLenArg
  keeps : Keeps [.eax, .edi] s t
  outside : Outside base 0 size s.mem t.mem

theorem verifyingEntry_ok {s : State} (A : VerifyingABI s) :
    WP isa (.block Entry.verifyEntry) s fun t =>
      Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s t := by
  have sz : 8272 ≤ (arg s 9).toNat * 8 := by have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega
  apply WP.mono (installArguments_ok Entry.verifyArguments (scratchArg := 8)
    (keyArg := 0) (pLenArg := 2) (qLenArg := 3)
    (A.stackArgument (by decide : 8 < 10)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide) (by decide))
  · intro t ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
    exact ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
  · intro a ha
    apply A.stackArgument
    simp only [Entry.verifyArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem signingEntry_ok {s : State} (A : SigningABI s) :
    WP isa (.block Entry.signEntry) s fun t =>
      Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t := by
  have sz : 8272 ≤ (arg s 10).toNat * 8 := by have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega
  apply WP.mono (installArguments_ok Entry.signArguments (scratchArg := 9)
    (keyArg := 2) (pLenArg := 4) (qLenArg := 6)
    (A.stackArgument (by decide : 9 < 11)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide) (by decide))
  · intro t ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
    exact ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
  · intro a ha
    apply A.stackArgument
    simp only [Entry.signArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Dsa.X86
