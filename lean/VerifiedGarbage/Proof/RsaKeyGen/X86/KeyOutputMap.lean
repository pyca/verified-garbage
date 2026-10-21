module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO

/-! # The seven output slots name distinct persistent arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG.Impl.RsaKeyGen.X86.Key

theorem outputIndex_bound {i : Nat} (hi : i < 7) : outputIndex i < 32 := by
  exact (by decide : ∀ k : Fin 7, outputIndex k.val < 32) ⟨i, hi⟩

theorem outputIndex_zero {i : Nat} (hi : i < 7) : VG.Impl.Rsa.X86.Keys.aZero ≠ outputIndex i := by
  exact (by decide : ∀ k : Fin 7, VG.Impl.Rsa.X86.Keys.aZero ≠ outputIndex k.val) ⟨i, hi⟩

theorem outputIndex_injective {i j : Nat} (hi : i < 7) (hj : j < 7) (ne : i ≠ j) :
    outputIndex i ≠ outputIndex j := by
  exact (by decide : ∀ a b : Fin 7, a ≠ b → outputIndex a.val ≠ outputIndex b.val)
    ⟨i, hi⟩ ⟨j, hj⟩ (fun equal => ne (congrArg Fin.val equal))

end VG.Proof.RsaKeyGen.X86.Key
