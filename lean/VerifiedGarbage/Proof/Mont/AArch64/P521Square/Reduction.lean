module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMachine
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate

@[expose] public section
set_option exponentiation.threshold 1024
namespace VG.Proof.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64

abbrev outputWords (s : State) : List Word := (List.range 9).map (wordsAt s)

theorem output_eq {s : State} {xs : List Word} (hl : xs.length = 9)
    (h : ∀ i < 9, wordsAt s i = xs.getD i 0) : outputWords s = xs := by
  apply List.ext_getElem
  · simpa using hl.symm
  · intro i hi hi'
    have hi9 : i < 9 := by simpa using hi
    simpa only [outputWords, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] using h i hi9

theorem corrected_length (xs : List Word) (c : Bool) (hl : xs.length = 9) :
    (corrected xs c).length = 9 := by
  have hr := addWords_length xs (List.replicate 9 (~~~(0 : Word))) c (by simpa using hl)
  simp only [corrected, List.length_append, List.length_take, List.length_singleton, hr, hl]
  rfl

theorem input_regs (s : State) : inputValue (wordsAt s) = regsVal s uRegs := rfl

theorem output_regs (s : State) : value (outputWords s) = regsVal s (uRegs.take 9) := rfl

/-- Exact fold, conditional correction, and cyclic Montgomery rotation. -/
theorem reduction_ok (s : State) (hz : s.gpr .x30 = 0)
    (hu : regsVal s uRegs < fieldPrime*fieldPrime) :
    WP isa (.block (foldCode ++ correctCode ++ rotateCode)) s fun t =>
      regsVal t (uRegs.take 9) < fieldPrime ∧
      regsVal t (uRegs.take 9) * montBase % fieldPrime = regsVal s uRegs % fieldPrime ∧
      Keeps reduceClob s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (fold_ok s hz) fun s₁ ⟨h₁, c₁, z₁, k₁⟩ => ?_
  have hl : (folded (wordsAt s)).1.length = 9 := addWords_length _ _ _ rfl
  have e₁ := output_eq hl h₁
  rw [WP.block_append_iff]
  refine WP.mono (correct_ok s₁ z₁) fun s₂ ⟨h₂, k₂⟩ => ?_
  have e₂ := output_eq (corrected_length (outputWords s₁) s₁.c rfl) h₂
  rw [e₁, c₁] at e₂
  have hv : value (outputWords s₂) = regsVal s uRegs % fieldPrime := by
    rw [e₂, corrected_value (wordsAt s) (by simpa only [input_regs] using hu), input_regs]
  have hb : value (outputWords s₂) < fieldPrime := by
    rw [hv]
    exact Nat.mod_lt _ (by decide)
  refine WP.mono (rotate_ok s₂) fun t ⟨h₃, k₃⟩ => ?_
  have hlen : (rotated (wordsAt s₂)).length = 9 := rfl
  have e₃ := output_eq hlen h₃
  have hr := rotated_value (wordsAt s₂) (by change value (outputWords s₂) < _; exact Nat.lt_trans hb (by decide))
  have hm := rotation_mod hb
  rw [← hr, ← e₃, output_regs] at hm
  exact ⟨hm.1, hm.2.trans hv, k₁.trans (k₂.trans k₃)⟩

end VG.Proof.Mont.AArch64.P521Square
