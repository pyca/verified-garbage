module

public import VerifiedGarbage.Proof.Dsa.X86.SigningInstalled
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation

/-! # Complete functional and cdecl verification of the x86 signer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingOperation_spec {s : State} (A : SigningABI s) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (Entry.operation true) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) ((arg s 10).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  dsimp only
  have sz : 8272 ≤ (arg s 10).toNat * 8 := by have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega
  unfold Entry.operation Core.sequence
  dsimp only [List.foldr, ite_true]
  refine WP.seq (WP.mono (signingEntry_ok A) fun t I => ?_)
  refine WP.seq (widthDispatch_ok true _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (4, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (6, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (signingInstalled_spec A J) fun v ⟨Value, Bytes, K, O, Saved⟩ => ?_
  have Ov : StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0)
      ((arg s 10).toNat * 8) (arg s 1).toNat s.mem v.mem := by
    intro a hb ho hstack
    have H := A.used
    exact (O a (by omega) (by rw [← A.outLength]; exact ho) (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by omega)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, ?_, restored_abi R Esp (outputFrame_return Ov A.retScratch A.retOut A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem, A.outLength]; exact Bytes
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86
