module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! ### `Dsa.X86.CheckingABI`, which this module and modules that import it used -/

section

/-! # Domain-checking resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

structure CheckingABI (s : State) : Prop where
  stackLow : 108 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 4, (arg s 5).toNat * 8⟩, ⟨argAddr s 0, 24⟩]
  keyScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  keyBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  scratchBound : (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 2).toNat (arg s 3).toNat
  keyLength : (arg s 1).toNat = 2 * (arg s 2).toNat + (arg s 3).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 2).toNat ≤ (arg s 5).toNat

theorem checkingABI_of {s : State} (h : (Proof.Dsa.checkParametersContract abi 108).pre s) : CheckingABI s := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CheckingResources`, which this module and modules that import it used -/

section

/-! # Stack and workspace resources of domain checking -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CheckingABI.used {s : State} (A : CheckingABI s) : usedBytes ≤ (arg s 5).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega_using [L, H]

theorem CheckingABI.stackArgument {s : State} (A : CheckingABI s) {i : Nat} (hi : i < 6) :
    StackArgument s (argumentPointer s 4) ((arg s 5).toNat * 8) i := by
  apply stackArgument_of (count := 6) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem CheckingABI.stack {s : State} (A : CheckingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 108) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem CheckingABI.room {s : State} (A : CheckingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

end VG.Proof.Dsa.X86

end

end

/-! # Install the domain-checking cdecl arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingEntry_ok {s : State} (A : CheckingABI s) :
    WP isa (.block Generate.checkEntry) s fun t =>
      Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
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
