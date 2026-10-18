module

public import VerifiedGarbage.Proof.Dsa.X86.VerifyingInstalled
public import VerifiedGarbage.Proof.Dsa.X86.WidthDispatch
public import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame

/-! # Complete functional and cdecl verification of the x86 verifier -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem supportedWidths_member {pLen qLen : Nat} (H : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  unfold Spec.Dsa.lengthsValid at H
  omega

theorem verifyingOperation_spec {s : State} (A : VerifyingABI s) :
    WP isa (Entry.operation false) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  have sz : 8272 ≤ (arg s 9).toNat * 8 := by have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega
  unfold Entry.operation Core.sequence
  dsimp only [List.foldr, Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (verifyingEntry_ok A) fun t I => ?_)
  refine WP.seq (widthDispatch_ok false _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (verifyingInstalled_spec A J) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem v.mem :=
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
