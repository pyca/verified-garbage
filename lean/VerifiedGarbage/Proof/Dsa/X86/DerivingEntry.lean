module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.DerivingResources

/-! # Install the domain-deriving cdecl arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingEntry_precise {s : State} (A : DerivingABI s) :
    WP isa (.block Generate.deriveEntry) s fun t =>
      Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t ∧ Outside (argumentPointer s 7) 0 8272 s.mem t.mem := by
  have sz : 8272 ≤ (arg s 8).toNat * 8 := by have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega
  apply WP.mono (installArguments_precise Generate.deriveArguments (scratchArg := 7)
    (keyArg := 2) (pLenArg := 4) (qLenArg := 6)
    (A.stackArgument (by decide : 7 < 9)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide) (by decide))
  · intro t ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
    exact ⟨⟨Scr, Saved, Args, Q, G, Y, X, K, O.mono (Nat.le_refl _) (by omega)⟩,O⟩
  · intro a ha
    apply A.stackArgument
    simp only [Generate.deriveArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem derivingEntry_ok {s : State} (A : DerivingABI s) :
    WP isa (.block Generate.deriveEntry) s fun t =>
      Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t :=
  WP.mono (derivingEntry_precise A) fun _ H => H.1

end VG.Proof.Dsa.X86
