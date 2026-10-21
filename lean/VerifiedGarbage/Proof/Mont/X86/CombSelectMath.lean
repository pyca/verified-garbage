module

import VerifiedGarbage.Proof.Mont.X86.WindowSelect
public import Init.Data.BitVec.Basic

/-! Wordwise masked comb lookup reuses the window equality masks. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic

/-- Accumulating the fixed-address loads returns the selected word, or zero
until its entry has been visited. No secret table index is needed. -/
theorem masked_words_prefix (value : Nat → BitVec 32) (index count : Nat) :
    (List.range count).foldl (fun acc j =>
      acc ||| (value j &&& (if index = j then BitVec.allOnes 32 else 0#32))) 0#32 =
      if index < count then value index else 0#32 := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    by_cases eq : index = count
    · subst index
      simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte, BitVec.and_allOnes, BitVec.zero_or]
    · have same : index < count + 1 ↔ index < count := by omega
      simp only [eq, ↓reduceIte, BitVec.and_zero, BitVec.or_zero, same]

/-- The actual subtract/shift mask used by x86 has the same lookup result
for all 32 entries of the shared RSA comb. -/
theorem masked_words_lookup (value : Nat → BitVec 32) {index : Nat} (hi : index < 32) :
    (List.range 32).foldl (fun acc j =>
      acc ||| (value j &&& (0#32 - (((BitVec.ofNat 32 index ^^^ BitVec.ofNat 32 j) - 1) >>> 31)))) 0#32 =
      value index := by
  have same : ∀ j ∈ List.range 32, ∀ acc : BitVec 32,
      acc ||| (value j &&& (0#32 - (((BitVec.ofNat 32 index ^^^ BitVec.ofNat 32 j) - 1) >>> 31))) =
      acc ||| (value j &&& (if index = j then BitVec.allOnes 32 else 0#32)) := by
    intro j hj acc
    exact congrArg (fun mask : BitVec 32 => acc ||| (value j &&& mask))
      (window_mask_small index hi j (List.mem_range.mp hj))
  have congr_fold {f g : BitVec 32 → Nat → BitVec 32} (l : List Nat)
      (eq : ∀ j ∈ l, ∀ acc, f acc j = g acc j) : ∀ acc, l.foldl f acc = l.foldl g acc := by
    induction l with
    | nil => intro acc; rfl
    | cons j l ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [eq j (by simp), ih (fun k hk => eq k (by simp [hk]))]
  rw [congr_fold (List.range 32) same, masked_words_prefix, ite_eq_left hi]

end VG.Proof.Mont.X86.Dynamic
