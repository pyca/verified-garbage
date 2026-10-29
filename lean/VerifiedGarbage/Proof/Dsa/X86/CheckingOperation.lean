module

public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Dsa.X86.Installed

import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.CheckingResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.CheckingEntry
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.CheckingSized
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
/-! # Complete functional and cdecl verification of the x86 domain checker -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CheckingInstalled.lean`, which only this module imported.
section

/-! # Installed domain arguments agree with the caller's packed bytes -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingInstalled_spec {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t) :
    WP isa (Generate.checkSized (arg s 2).toNat (arg s 3).toNat) t fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) usedBytes t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  exact checkingSized_spec I.scr A.used A.lengths P Q G rfl rfl rfl
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength) Value

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingOperationWith_spec (sized : Nat → Nat → Prog isa) (Invariant : State → Mem → Prop)
    (installed : ∀ {s t : State} (_ : CheckingABI s),
      Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s t →
      WP isa (sized (arg s 2).toNat (arg s 3).toNat) t fun sf =>
        (sf.gpr .eax).toNat=(if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
        Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat*8) t.mem sf.mem ∧
        (Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)=true → Invariant s sf.mem) ∧
        ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
          VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters)
    {s : State} (A : CheckingABI s) :
    WP isa (Generate.checkParametersWith sized) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr ∧
      (Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)=true → Invariant s sf.mem) := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  unfold Generate.checkParametersWith Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (checkingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok sized _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (installed A J) fun v ⟨Value, K, O, Inv, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a ha
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_, by rw [R.mem]; exact Inv⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

theorem checkingOperation_spec {s : State} (A : CheckingABI s) :
    WP isa (Generate.checkParameters) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  refine WP.mono (checkingOperationWith_spec Generate.checkSized (fun _ _ => True) ?_ A) ?_
  · intro s t A I
    exact WP.mono (checkingInstalled_spec A I) fun sf ⟨V,K,O,S⟩ =>
      ⟨V,K,(fun a ha hs => O a (by have := A.used; omega) hs), (fun _ => trivial), S⟩
  · intro t ⟨V,K,O,R,W,_⟩
    exact ⟨V,K,O,R,W⟩

end VG.Proof.Dsa.X86
