module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame

/-! ### `Dsa.X86.DerivingResources`, which this module and modules that import it used -/

section

/-! # Stack and workspace resources of key derivation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem DerivingABI.used {s : State} (A : DerivingABI s) : usedBytes ≤ (arg s 8).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega_using [L, H]

theorem DerivingABI.stackArgument {s : State} (A : DerivingABI s) {i : Nat} (hi : i < 9) :
    StackArgument s (argumentPointer s 7) ((arg s 8).toNat * 8) i := by
  apply stackArgument_of (count := 9) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem DerivingABI.stack {s : State} (A : DerivingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 7) ((arg s 8).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 108) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 7).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem DerivingABI.room {s : State} (A : DerivingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 7) ((arg s 8).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

end VG.Proof.Dsa.X86

end

end

/-! # Install the domain-deriving cdecl arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingEntry_precise {s : State} (A : DerivingABI s) :
    WP isa (.block Generate.deriveEntry) s fun t =>
      Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t ∧ Outside (argumentPointer s 7) 0 8272 s.mem t.mem := by
  have sz : 8272 ≤ (arg s 8).toNat * 8 := by have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega_using [H]
  apply WP.mono (installArguments_precise Generate.deriveArguments (scratchArg := 7)
    (keyArg := 2) (pLenArg := 4) (qLenArg := 6)
    (A.stackArgument (by decide : 7 < 9)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide) (by decide))
  · intro t ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
    exact ⟨⟨Scr, Saved, Args, Q, G, Y, X, K, O.mono (Nat.le_refl _) (by omega_using [sz])⟩,O⟩
  · intro a ha
    apply A.stackArgument
    simp only [Generate.deriveArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Dsa.X86
