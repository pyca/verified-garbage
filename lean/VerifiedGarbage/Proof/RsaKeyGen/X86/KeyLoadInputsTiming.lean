module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadExponentTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputInitialize
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportExponent
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The complete native import prefix has public control flow and addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key

theorem clearInputPair_trace (E : Environment) : RelCT isa (InputPair E) (clearArrays E.n) (InputPair E) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, _⟩ := clearArrays_trace E.n _ _ _ _ _ _
    (taint.le_sound (by rfl) P.agree) A C
  obtain ⟨leftInput, _, _, _, leftKeeps⟩ := wp_result P.left.initialize_ok A
  obtain ⟨rightInput, _, _, _, rightKeeps⟩ := wp_result P.right.initialize_ok C
  refine ⟨trace, leftInput, rightInput, ?_⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.stack

theorem primeInputPair_trace (E : Environment) (i out : Nat) (index : i = 2 ∨ i = 3)
    (ho : out < 32) (persistent : 15 ≤ out) :
    RelCT isa (InputPair E) (loadPrime E.n (8 * i) out) (InputPair E) := by
  intro s t tr ur u v P A C
  have hi : 2 * i < 18 := by omega
  have code : 4 * (2 * i) = 8 * i := by omega
  have raw := loadPrime_trace E (2 * i) out hi
  rw [code] at raw
  obtain ⟨trace, _⟩ := raw _ _ _ _ _ _ P A C
  obtain ⟨leftInput, _, _, _, _, leftKeeps⟩ := wp_result (P.left.importPrime index ho persistent) A
  obtain ⟨rightInput, _, _, _, _, rightKeeps⟩ := wp_result (P.right.importPrime index ho persistent) C
  refine ⟨trace, leftInput, rightInput, ?_⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.stack

theorem exponentInputPair_trace (E : Environment) :
    RelCT isa (InputPair E) (loadExponent E.n)
      (fun s t => InputPair E s t ∧ VG.X86.Taint.Agree (workspaceTaint true) s t) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := loadExponent_trace E _ _ _ _ _ _ P A C
  obtain ⟨leftInput, _, _, _, _, leftKeeps⟩ := wp_result P.left.importExponent A
  obtain ⟨rightInput, _, _, _, _, rightKeeps⟩ := wp_result P.right.importExponent C
  refine ⟨trace, ⟨leftInput, rightInput, ?_⟩, agree⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.stack

theorem inputCode_trace (E : Environment) :
    RelCT isa (InputPair E) (inputCode E.n)
      (fun s t => InputPair E s t ∧ VG.X86.Taint.Agree (workspaceTaint true) s t) := by
  unfold inputCode
  exact RelCT.seq (RelCT.seq (RelCT.seq (clearInputPair_trace E)
    (primeInputPair_trace E 2 aPa (Or.inl rfl) (by decide) (by decide)))
    (primeInputPair_trace E 3 aQa (Or.inr rfl) (by decide) (by decide))) (exponentInputPair_trace E)

end VG.Proof.RsaKeyGen.X86.Key
