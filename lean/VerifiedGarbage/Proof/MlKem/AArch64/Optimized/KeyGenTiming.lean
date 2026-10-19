module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables

/-! # Constant-time key generation under the emitted read-only table contract -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.KeyGen
variable {P : KemLay} {keccak : Sha3.AArch64.Permutation}

theorem entry_symbols {base : Contract isa} {s u : State} (h : (entryContract base).pub s u) :
    (s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE") ∧
    ∀name∈restSymbols,s.syms name=u.syms name := by
  refine ⟨h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inl rfl),?_⟩
  intro name hn
  simp only [restSymbols,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inl rfl))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))

end VG.Proof.MlKem.AArch64.Optimized
