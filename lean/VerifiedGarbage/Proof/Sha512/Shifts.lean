import VerifiedGarbage.Proof.Sha512.Spec

/-!
# SHA-512: `Σ`, `σ` and `Maj` as code without rotations computes them

Without a rotation instruction, a rotation is the exclusive or of a shift each
way. The shifts of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` are chained, as SIMD code computes
them: one copy of the word is shifted right by each term's amount in turn,
another left (`chain5`, `chain6`). `Maj(a, b, c)` is `((a ⊕ b) ∧ (b ⊕ c)) ⊕ b`,
which lets a round reuse the previous round's `a ⊕ b` as its `b ⊕ c`.
-/

namespace VG.Proof.Sha512

open VG.Spec.Sha512 (Word bsig0 bsig1 ssig0 ssig1 maj ch)

/-- A rotation as the xor of a shift each way. -/
theorem rotateRight_eq_shifts (x : Word) {n : Nat} (h0 : 0 < n) (h : n < 64) :
    x.rotateRight n = x >>> n ^^^ x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_rotateRight _ _ hi]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    decide_eq_true hi, Bool.true_and]
  by_cases hl : i < 64 - n
  · rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm, decide_eq_true hl]
    simp only [Bool.not_true, Bool.false_and, Bool.xor_false]
  · rw [BitVec.getLsbD_of_ge x (n + i) (by omega), decide_eq_false hl, Bool.not_false, Bool.true_and,
      Bool.false_xor]
    exact congrArg x.getLsbD (by omega)

/-- The five terms of `σ₀` or `σ₁` as chained shifts: right by `r₁`, `r₁ + r₂`,
`r₁ + r₂ + r₃` and left by `l₁`, `l₁ + l₂`, in the order the code combines them. -/
def chain5 (x : Word) (r₁ l₁ r₂ l₂ r₃ : Nat) : Word :=
  x >>> r₁ ^^^ x <<< l₁ ^^^ x >>> r₁ >>> r₂ ^^^ x <<< l₁ <<< l₂ ^^^ x >>> r₁ >>> r₂ >>> r₃

/-- The six terms of `Σ₀` or `Σ₁`: `chain5` and a third left shift. -/
def chain6 (x : Word) (r₁ l₁ r₂ l₂ r₃ l₃ : Nat) : Word :=
  chain5 x r₁ l₁ r₂ l₂ r₃ ^^^ x <<< l₁ <<< l₂ <<< l₃

theorem xor_left_comm (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem bsig1_chain (x : Word) : chain6 x 14 23 4 23 23 4 = bsig1 x := by
  simp only [chain6, chain5, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [bsig1, rotateRight_eq_shifts x (n := 14) (by decide) (by decide),
    rotateRight_eq_shifts x (n := 18) (by decide) (by decide),
    rotateRight_eq_shifts x (n := 41) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

theorem bsig0_chain (x : Word) : chain6 x 28 25 6 5 5 6 = bsig0 x := by
  simp only [chain6, chain5, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [bsig0, rotateRight_eq_shifts x (n := 28) (by decide) (by decide),
    rotateRight_eq_shifts x (n := 34) (by decide) (by decide),
    rotateRight_eq_shifts x (n := 39) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

theorem ssig1_chain (x : Word) : chain5 x 6 3 13 42 42 = ssig1 x := by
  simp only [chain5, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [ssig1, rotateRight_eq_shifts x (n := 19) (by decide) (by decide),
    rotateRight_eq_shifts x (n := 61) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

theorem ssig0_chain (x : Word) : chain5 x 1 56 6 7 1 = ssig0 x := by
  simp only [chain5, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [ssig0, rotateRight_eq_shifts x (n := 1) (by decide) (by decide),
    rotateRight_eq_shifts x (n := 8) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

theorem maj_xor (a b c : Word) : (a ^^^ b) &&& (b ^^^ c) ^^^ b = maj a b c := by
  ext i; simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

end VG.Proof.Sha512
