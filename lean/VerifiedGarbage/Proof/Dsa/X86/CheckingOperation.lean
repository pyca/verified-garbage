module
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Dsa.X86.CheckingInstalled
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.CheckingResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.CheckingEntry

/-! # Complete functional and cdecl verification of the x86 domain checker -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingOperation_spec {s : State} (A : CheckingABI s) :
    WP isa (Generate.checkParameters) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  unfold Generate.checkParameters Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (checkingEntry_ok A) fun t I => ?_)
  refine WP.seq (checkDispatch_ok _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (checkingInstalled_spec A J) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a (by have := A.used; omega)
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86
