module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyCrt
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstantTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesTiming

/-! # CRT assembly keeps factors, residues, and inverse choices secret -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem divisorOf_public (n input : Nat) : KeyPublic (divisorOf n input) :=
  (constArray_public ..).seq ((eqS_public ..).seq (sel_public ..))

theorem qinvPart_public (n : Nat) : KeyPublic (qinvPart n) := by
  unfold qinvPart
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact oddModulus_public ..
  · exact inverseFrom_public ..
  · exact gcdIsOne_public _
  · exact ⟨.block [], workspaceTaint true, rfl, rfl⟩
  · exact widenCopy_public ..

theorem crtPart_public (n : Nat) : KeyPublic (crtPart n) :=
  (divisorOf_public ..).seq ((divisionFrom_public ..).seq
    ((divisorOf_public ..).seq (divisionFrom_public ..)))

theorem nPart_public (n : Nat) : KeyPublic (nPart n) := primeProduct_public ..

theorem smallMask_public (n : Nat) : KeyPublic (smallMask n) := by
  refine (constArray_public ..).seq ((sub3_public ..).seq ?_)
  exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

end VG.Proof.RsaKeyGen.X86.Key
