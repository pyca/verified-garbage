import VerifiedGarbage.Proof.Blowfish.Schedule

/-!
# F, one S-box at a time

`fAcc K x j`: F's value after its first `j + 1` S-boxes (S₁[a], + S₂[b],
XOR S₃[c], + S₄[d]); `fAcc K x 3 = f K x`. `quarter x j` is the byte of `x`
that indexes S-box `j`: byte `3 - j`.
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- The byte of `x` that indexes S-box `j`: `a`, `b`, `c` or `d`. -/
def quarter (x : Word) (j : Nat) : Byte := x.extractLsb' (8 * (3 - j)) 8

/-- S-box `j` of `x`'s quarter. -/
def sq (K : Schedule) (x : Word) (j : Nat) : Word := sEntry K j (quarter x j)

def fAcc (K : Schedule) (x : Word) : Nat → Word
  | 0 => sq K x 0
  | 1 => sq K x 0 + sq K x 1
  | 2 => (sq K x 0 + sq K x 1) ^^^ sq K x 2
  | _ => ((sq K x 0 + sq K x 1) ^^^ sq K x 2) + sq K x 3

theorem fAcc_succ (K : Schedule) (x : Word) {j : Nat} (hj : j < 3) :
    fAcc K x (j + 1) = if j + 1 = 2 then fAcc K x j ^^^ sq K x (j + 1) else fAcc K x j + sq K x (j + 1) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

theorem shift_setWidth (x : Word) (k : Nat) : (x >>> k).setWidth 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem fAcc_three (K : Schedule) (x : Word) : fAcc K x 3 = f K x := by
  have h0 : x.setWidth 8 = x.extractLsb' 0 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  simp only [fAcc, sq, f, quarter, shift_setWidth x 24, shift_setWidth x 16, shift_setWidth x 8, h0,
    Nat.reduceSub, Nat.reduceMul]

end VG.Proof.Blowfish
