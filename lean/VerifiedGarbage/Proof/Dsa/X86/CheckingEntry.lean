module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.CheckingResources

/-! # Install the domain-checking cdecl arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingEntry_ok {s : State} (A : CheckingABI s) :
    WP isa (.block Generate.checkEntry) s fun t =>
      Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  apply WP.mono (installArguments_ok Generate.checkArguments (scratchArg := 4)
    (keyArg := 0) (pLenArg := 2) (qLenArg := 3)
    (A.stackArgument (by decide : 4 < 6)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide) (by decide))
  · intro t ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
    exact ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
  · intro a ha
    apply A.stackArgument
    simp only [Generate.checkArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Dsa.X86
