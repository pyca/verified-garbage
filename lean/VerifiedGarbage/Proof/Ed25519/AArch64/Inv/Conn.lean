module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Row
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Mat

/-! # The inversion's rows as integers

A row of the code (`row_ok`) for the matrix entries `m₁`, `m₂` as `mat`
leaves them (magnitudes and masks) is `m₁ X + m₂ Y` modulo `2³²⁰`: `X`, `Y`
signed for the rows of `f` and `g` (`rowF_int`), unsigned for those of `u`
and `v` (`rowU_int`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem maskN_cases (w : Word) : (w.msb = true ∧ maskN w = BitVec.allOnes 64) ∨
    (w.msb = false ∧ maskN w = 0) := by
  unfold maskN; cases w.msb <;> simp

theorem flip4_eq (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    flip4 m base o (maskN w) = flipN w (fe m base o) := by
  unfold flipN
  have l0 := (word m base o).isLt
  have l1 := (word m base (o + 8)).isLt
  have l2 := (word m base (o + 16)).isLt
  have l3 := (word m base (o + 24)).isLt
  rcases maskN_cases w with ⟨h, e⟩ | ⟨h, e⟩
  · simp only [flip4, e, h, ↓reduceIte, BitVec.xor_allOnes, val4, fe, BitVec.toNat_not]
    omega
  · simp only [flip4, e, h, Bool.false_eq_true, ↓reduceIte, val4, fe, BitVec.toNat_xor,
      show (0 : Word).toNat = 0 from rfl, Nat.xor_zero]

theorem top_msb (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    (word m base (o + 24) ^^^ maskN w).msb = decide (2 ^ 255 ≤ flipN w (fe m base o)) := by
  rw [← flip4_eq]
  have l0 := (word m base o ^^^ maskN w).isLt
  have l1 := (word m base (o + 8) ^^^ maskN w).isLt
  have l2 := (word m base (o + 16) ^^^ maskN w).isLt
  rw [BitVec.msb_eq_decide]
  simp only [flip4, val4]
  congr 1
  apply propext
  omega

theorem corrV_true_eq (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    (corrV true (word m base (o + 24) ^^^ maskN w) (absW w) (maskN w)).toNat =
      topN w (fe m base o) := by
  simp only [corrV, ↓reduceIte, mask_eq]
  unfold topN
  have hm : maskN (word m base (o + 24) ^^^ maskN w) =
      if 2 ^ 255 ≤ flipN w (fe m base o) then BitVec.allOnes 64 else 0 := by
    rw [maskN, top_msb]; simp only [decide_eq_true_eq]
  rw [hm]
  split
  · rw [BitVec.allOnes_and, absN_word]
  · rw [BitVec.toNat_and, show (0 : Word).toNat = 0 from rfl, Nat.zero_and]

theorem corrV_false_eq (x : Word) (w : Word) :
    (corrV false x (absW w) (maskN w)).toNat = negN w := by
  simp only [corrV, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.and_comm]
  exact negN_word w

theorem negN_le_absN (w : Word) : negN w ≤ absN w := by unfold negN; split <;> omega

theorem flipN_lt (w : Word) {X : Nat} (hX : X < 2 ^ 256) : flipN w X < 2 ^ 256 := by
  unfold flipN; split <;> omega

/-- The carry of two entries, below `2⁶⁴`. -/
theorem car_eq (a b : Word) (h : absN a + absN b < 2 ^ 64) :
    ((absW a &&& maskN a) + (absW b &&& maskN b)).toNat = negN a + negN b := by
  rw [BitVec.toNat_add, negN_word, negN_word]
  have := negN_le_absN a; have := negN_le_absN b
  exact Nat.mod_eq_of_lt (by omega)

/-- A row of `f` and `g` as integers. -/
theorem rowF_int {a b : Word} {X Y W : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (h : (W + 2 ^ 256 * (topN a X + topN b Y)) % (2 ^ 256 * 2 ^ 64) =
      (negN a + negN b + flipN a X * absN a + flipN b Y * absN b) % (2 ^ 256 * 2 ^ 64)) :
    (W : Int) % 2 ^ 320 = (a.toInt * sv X + b.toInt * sv Y) % 2 ^ 320 := by
  have e1 := fterm a hX
  have e2 := fterm b hY
  rw [Nat.mul_comm (absN a) (flipN a X)] at e1
  rw [Nat.mul_comm (absN b) (flipN b Y)] at e2
  generalize flipN a X * absN a = P1 at e1 h
  generalize flipN b Y * absN b = P2 at e2 h
  rw [show (2 : Int) ^ 320 = 2 ^ 256 * 2 ^ 64 by rw [← pow_add]]
  omega

/-- A row of `u` and `v` as integers. -/
theorem rowU_int {a b : Word} {X Y W : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (h : (W + 2 ^ 256 * (negN a + negN b)) % (2 ^ 256 * 2 ^ 64) =
      (negN a + negN b + flipN a X * absN a + flipN b Y * absN b) % (2 ^ 256 * 2 ^ 64)) :
    (W : Int) % 2 ^ 320 = (a.toInt * X + b.toInt * Y) % 2 ^ 320 := by
  have e1 := uterm a hX
  have e2 := uterm b hY
  rw [Nat.mul_comm (absN a) (flipN a X)] at e1
  rw [Nat.mul_comm (absN b) (flipN b Y)] at e2
  generalize flipN a X * absN a = P1 at e1 h
  generalize flipN b Y * absN b = P2 at e2 h
  rw [show (2 : Int) ^ 320 = 2 ^ 256 * 2 ^ 64 by rw [← pow_add]]
  omega

end VG.Proof.Ed25519.AArch64.Inv
