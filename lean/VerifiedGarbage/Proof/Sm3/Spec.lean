import VerifiedGarbage.Spec.Sm3
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SM3: lemmas about the specification
-/

namespace VG.Proof.Sm3

open VG.Spec.Sm3

/-! ## The message expansion -/

theorem expand_succ (B : Block) (j : Nat) : expand B (j + 1) = W B j :: expand B j := rfl

theorem expand_length (B : Block) (j : Nat) : (expand B j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [expand_succ, List.length_cons, ih]

theorem expand_getElem! (B : Block) {j i : Nat} (hi : i < j) :
    (expand B j)[i]! = W B (j - 1 - i) := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
    rw [expand_succ]
    cases i with
    | zero => simp
    | succ i =>
      simp only [getElem!_pos (W B j :: expand B j) (i + 1) (by
          simp only [List.length_cons, expand_length]; omega),
        List.getElem_cons_succ]
      rw [← getElem!_pos, ih (by omega)]
      congr 1; omega

theorem W_lt (B : Block) {j : Nat} (h : j < 16) : W B j = B ⟨j, h⟩ := by
  simp [W, expand, h]

theorem W_ge (B : Block) {j : Nat} (h : 16 ≤ j) :
    W B j = p1 (W B (j - 16) ^^^ W B (j - 9) ^^^ (W B (j - 3)).rotateLeft 15) ^^^
      (W B (j - 13)).rotateLeft 7 ^^^ W B (j - 6) := by
  show (expand B (j + 1)).headD 0 = _
  simp only [expand, show ¬ j < 16 by omega, dite_false, List.headD_cons]
  rw [expand_getElem! B (by omega), expand_getElem! B (by omega),
    expand_getElem! B (by omega), expand_getElem! B (by omega), expand_getElem! B (by omega),
    show j - 1 - 15 = j - 16 by omega, show j - 1 - 8 = j - 9 by omega,
    show j - 1 - 2 = j - 3 by omega, show j - 1 - 12 = j - 13 by omega,
    show j - 1 - 5 = j - 6 by omega]

/-! ## Iterations -/

/-- One iteration `j` with explicit `W_j` (`w`) and `W_{j+4}` (`w₄`). -/
def roundW (v : HashValue) (j : Nat) (w w₄ : Word) : HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]
  let e := v[4]; let f := v[5]; let g := v[6]; let h := v[7]
  let ss1 := (a.rotateLeft 12 + e + (T j).rotateLeft (j % 32)).rotateLeft 7
  let ss2 := ss1 ^^^ a.rotateLeft 12
  let tt1 := ff j a b c + d + ss2 + (w ^^^ w₄)
  let tt2 := gg j e f g + h + ss1 + w
  #v[tt1, a, b.rotateLeft 9, c, p0 tt2, e, f.rotateLeft 19, g]

/-! The words of `roundW`, for rewriting without unfolding the vector literal. -/
section
variable (v : HashValue) (j : Nat) (w w₄ : Word)
theorem roundW_0 : (roundW v j w w₄)[0] =
    ff j v[0] v[1] v[2] + v[3] +
      ((v[0].rotateLeft 12 + v[4] + (T j).rotateLeft (j % 32)).rotateLeft 7 ^^^ v[0].rotateLeft 12) +
      (w ^^^ w₄) := rfl
theorem roundW_1 : (roundW v j w w₄)[1] = v[0] := rfl
theorem roundW_2 : (roundW v j w w₄)[2] = v[1].rotateLeft 9 := rfl
theorem roundW_3 : (roundW v j w w₄)[3] = v[2] := rfl
theorem roundW_4 : (roundW v j w w₄)[4] =
    p0 (gg j v[4] v[5] v[6] + v[7] +
      (v[0].rotateLeft 12 + v[4] + (T j).rotateLeft (j % 32)).rotateLeft 7 + w) := rfl
theorem roundW_5 : (roundW v j w w₄)[5] = v[4] := rfl
theorem roundW_6 : (roundW v j w w₄)[6] = v[5].rotateLeft 19 := rfl
theorem roundW_7 : (roundW v j w w₄)[7] = v[6] := rfl
end

theorem round_eq (B : Block) (v : HashValue) (j : Nat) :
    round B v j = roundW v j (W B j) (W B (j + 4)) := rfl

theorem rounds_zero (V : HashValue) (B : Block) : rounds V B 0 = V := rfl

theorem rounds_succ (V : HashValue) (B : Block) (j : Nat) :
    rounds V B (j + 1) = round B (rounds V B j) j := by
  simp [rounds, List.range_succ, List.foldl_append]

/-! ## Bitwise identities used by the implementations -/

theorem add_left_comm {n : Nat} (a b c : BitVec n) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

theorem xor_left_comm {n : Nat} (a b c : BitVec n) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

/-- Normalizes sums and exclusive ors (with `simp only`) up to associativity
and commutativity. -/
theorem ac {n : Nat} : (∀ a b c : BitVec n, a + b + c = a + (b + c)) ∧
    (∀ a b : BitVec n, a + b = b + a) ∧ (∀ a b c : BitVec n, a + (b + c) = b + (a + c)) ∧
    (∀ a b c : BitVec n, a ^^^ b ^^^ c = a ^^^ (b ^^^ c)) ∧
    (∀ a b : BitVec n, a ^^^ b = b ^^^ a) ∧ (∀ a b c : BitVec n, a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c)) :=
  ⟨BitVec.add_assoc, BitVec.add_comm, add_left_comm, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm⟩

/-- A rotation left is a rotation right by the complement. -/
theorem rotateLeft_eq (x : Word) {n : Nat} (h₀ : 0 < n) (h : n < 32) :
    x.rotateLeft n = x.rotateRight (32 - n) := by
  ext i hi
  rw [BitVec.getElem_rotateLeft hi, BitVec.getElem_rotateRight hi]
  simp only [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show 32 - n < 32 by omega)]
  by_cases h' : i < n
  · rw [dite_eq_left_of_eq_true (eq_true h'), dite_eq_left_of_eq_true (eq_true (by omega))]
  · rw [dite_eq_right_of_eq_false (eq_false h'), dite_eq_right_of_eq_false (eq_false (by omega))]
    congr 1; omega

theorem ff_lo {j : Nat} (h : j < 16) (x y z : Word) : ff j x y z = x ^^^ y ^^^ z := by
  simp [ff, h]

theorem gg_lo {j : Nat} (h : j < 16) (x y z : Word) : gg j x y z = x ^^^ y ^^^ z := by
  simp [gg, h]

/-- `FF_j` for `16 ≤ j`, as the implementations compute it. -/
theorem maj_eq (x y z : Word) : x &&& y ||| x &&& z ||| y &&& z = (x ||| y) &&& z ||| x &&& y := by
  ext i; simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

/-- `GG_j` for `16 ≤ j`, as the implementations compute it. -/
theorem ch_eq (x y z : Word) : x &&& y ||| ~~~x &&& z = (y ^^^ z) &&& x ^^^ z := by
  ext i; simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem ff_hi {j : Nat} (h : ¬ j < 16) (x y z : Word) : ff j x y z = (x ||| y) &&& z ||| x &&& y := by
  simp only [ff, h, ↓reduceIte, maj_eq]

theorem gg_hi {j : Nat} (h : ¬ j < 16) (x y z : Word) : gg j x y z = (y ^^^ z) &&& x ^^^ z := by
  simp only [gg, h, ↓reduceIte, ch_eq]

/-- The rotations of the specification, as the implementations compute them: rotations
right by the complement. -/
theorem rotl7 (x : Word) : x.rotateLeft 7 = x.rotateRight 25 := rotateLeft_eq x (by decide) (by decide)
theorem rotl9 (x : Word) : x.rotateLeft 9 = x.rotateRight 23 := rotateLeft_eq x (by decide) (by decide)
theorem rotl12 (x : Word) : x.rotateLeft 12 = x.rotateRight 20 := rotateLeft_eq x (by decide) (by decide)
theorem rotl15 (x : Word) : x.rotateLeft 15 = x.rotateRight 17 := rotateLeft_eq x (by decide) (by decide)
theorem rotl17 (x : Word) : x.rotateLeft 17 = x.rotateRight 15 := rotateLeft_eq x (by decide) (by decide)
theorem rotl19 (x : Word) : x.rotateLeft 19 = x.rotateRight 13 := rotateLeft_eq x (by decide) (by decide)
theorem rotl23 (x : Word) : x.rotateLeft 23 = x.rotateRight 9 := rotateLeft_eq x (by decide) (by decide)

/-- `TT1`, in the order the implementations add its terms. -/
theorem tt1_eq (d x y w f : Word) : d + (x ^^^ y) + w + f = f + d + (y ^^^ x) + w := by
  simp only [ac]

/-- `P_0(TT2)`, in the order the implementations add the terms of `TT2`. -/
theorem tt2_eq (h s w g : Word) :
    (h + s + w + g ^^^ (h + s + w + g).rotateRight 23) ^^^ (h + s + w + g).rotateRight 15 =
      p0 (g + h + s + w) := by
  rw [show h + s + w + g = g + h + s + w by simp only [ac]]
  simp only [Spec.Sm3.p0, rotl9, rotl17]

end VG.Proof.Sm3
