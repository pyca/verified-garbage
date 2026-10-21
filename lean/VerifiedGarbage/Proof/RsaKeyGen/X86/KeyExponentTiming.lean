module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstantTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductTiming

/-! # Private-exponent arithmetic has a fixed secret-independent schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem subtractPair_public (out a b : Nat) : KeyPublic (.block (subtractPair out a b)) := by
  let reference : Prog isa := .block (subtractPair 0 0 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  refine ⟨hint, workspaceTaint true, ?_, rfl⟩
  exact (check_of_erase_eq (.block (subtractPair out a b)) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)

theorem chain_public (n out a b : Nat) : KeyPublic (chainW .adc n out a b) := by
  let reference : Prog isa := chainW .adc 1 0 0 0
  let hint := VG.Taint.hintOf taint (workspaceTaint true) (Code.erase reference)
  let final : VG.X86.Taint.T := rowTaint true
  refine ⟨hint, final, ?_, by decide +kernel⟩
  exact (check_of_erase_eq (chainW .adc n out a b) reference (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)

theorem complement_public (n : Nat) : KeyPublic (complement n) := by
  exact (show KeyPublic (zerosW (slot n aDen) (n + 2)) from
    ⟨zerosHint true, zerosTaint true, zeros_check true _ _, rfl⟩).seq (subtractPair_public ..)

theorem correctionNumerator_public (n : Nat) : KeyPublic (correctionNumerator n) := by
  unfold correctionNumerator
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨Product.productHint true, Product.productEndTaint true,
      Product.product_check true _ _ _ _ _ _, rfl⟩
  · exact constArray_public ..
  · exact chain_public ..

theorem correction_public (n : Nat) : KeyPublic (correction n) := by
  unfold correction
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact correctionNumerator_public _
  · exact widenCopy_public ..
  · exact divisionCompute_public _
  · exact widenCopy_public ..

theorem dProduct_public (n : Nat) : KeyPublic (dProduct n) := by
  refine KeyPublic.seq ?_ (chain_public ..)
  exact ⟨Product.productHint true, Product.productEndTaint true,
    Product.product_check true _ _ _ _ _ _, rfl⟩

theorem gcdIsOne_public (n : Nat) : KeyPublic (gcdIsOne n) :=
  (constArray_public ..).seq (eqS_public ..)

theorem lAtLeastTwo_public (n : Nat) : KeyPublic (lAtLeastTwo n) := by
  refine (constArray_public ..).seq ((sub3_public ..).seq ?_)
  exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem dOddPrepare_public (n : Nat) : KeyPublic (dOddPrepare n) := by
  unfold dOddPrepare
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact divisionFrom_public ..
  · exact inverseFrom_public ..
  · exact gcdIsOne_public _
  · exact lAtLeastTwo_public _

theorem dOddFinish_public (n : Nat) : KeyPublic (dOddFinish n) :=
  (complement_public _).seq ((correction_public _).seq (dProduct_public _))

theorem dOdd_public (n : Nat) : KeyPublic (dOdd n) :=
  (dOddPrepare_public _).seq (dOddFinish_public _)

theorem dEven_public (n : Nat) : KeyPublic (dEven n) := by
  unfold dEven
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oddModulus_public ..
  · exact ⟨.block [], workspaceTaint true, rfl, rfl⟩
  · exact divisionFrom_public ..
  · exact inverseFrom_public ..
  · exact gcdIsOne_public _
  · exact ⟨.block [], workspaceTaint true, rfl, rfl⟩
  · exact copy_public ..

theorem dOne_public (n : Nat) : KeyPublic (dOne n) := by
  refine (copy_public ..).seq ((eqS_public ..).seq ?_)
  exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem dZero_public : KeyPublic dZero :=
  ⟨.block [], { regs := .ofList [.edi, .esi, .eax], flags := false }, rfl, rfl⟩

end VG.Proof.RsaKeyGen.X86.Key
