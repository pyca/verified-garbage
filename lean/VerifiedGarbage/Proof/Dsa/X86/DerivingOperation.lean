module
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.Installed

import VerifiedGarbage.Proof.Dsa.X86.DerivingInstalled
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.DerivingEntry
import VerifiedGarbage.Proof.Dsa.X86.DerivingResources

/-! # Complete functional and cdecl verification of the x86 signer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingOperationWith_spec (sized : Nat → Nat → Prog isa) {s : State} (A : DerivingABI s)
    (installed : ∀ {t : State},
      Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s t →
      Outside (argumentPointer s 7) 0 8272 s.mem t.mem →
      let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      WP isa (sized (arg s 4).toNat (arg s 6).toNat) t fun sf =>
        (sf.gpr .eax).toNat=Spec.Dsa.signStatus result ∧
        Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat=
          result.getD (List.replicate (arg s 1).toNat 0) ∧
        Keeps powerClob t sf ∧ StackOutputFrame (t.gpr .esp) (argumentPointer s 7)
          (argumentPointer s 0) usedBytes (arg s 1).toNat t.mem sf.mem ∧
        ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 7)) regs Entry.savedRegisters →
          VG.X86.Spill.Saved sf.mem (off (argumentPointer s 7)) regs Entry.savedRegisters) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa (Generate.deriveKeyWith sized) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 7) (argumentPointer s 0) ((arg s 8).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  dsimp only
  have sz : 8272 ≤ (arg s 8).toNat * 8 := by have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega
  unfold Generate.deriveKeyWith Core.sequence
  dsimp only [List.foldr, ite_true]
  refine WP.seq (WP.mono (derivingEntry_precise A) fun t ⟨I,Oentry⟩ => ?_)
  refine WP.seq (generationDispatch_ok sized _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (4, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (6, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (installed J (by rw [Ou]; exact Oentry)) fun v ⟨Value, Bytes, K, O, Saved⟩ => ?_
  have Ov : StackOutputFrame (s.gpr .esp) (argumentPointer s 7) (argumentPointer s 0)
      ((arg s 8).toNat * 8) (arg s 1).toNat s.mem v.mem := by
    intro a hb ho hstack
    have H := A.used
    exact (O a (by omega) ho (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by omega)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, ?_, restored_abi R Esp (outputFrame_return Ov A.retScratch A.retOut A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Bytes
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

theorem derivingOperation_spec {s : State} (A : DerivingABI s) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa (Generate.deriveKey) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 7) (argumentPointer s 0) ((arg s 8).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr :=
  derivingOperationWith_spec Generate.deriveSized A (fun I _ => derivingInstalled_spec A I)

end VG.Proof.Dsa.X86
