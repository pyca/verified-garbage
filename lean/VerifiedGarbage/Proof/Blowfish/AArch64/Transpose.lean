import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes

/-!
# Words to byte planes and back

`uzp_uzp`: two levels of `uzp1`/`uzp2` (as in `planes`) leave in byte `n`
of the result byte `o₁ + 2 o₂` of word `n` of four vectors (`o₁`, `o₂` 0 for
`uzp1` and 1 for `uzp2`). `zip_zip`: two levels of `zip1`/`zip2` (as in
`words`) turn four byte planes back into sixteen words.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

/-- `uzp1` (`o = 0`) or `uzp2` (`o = 1`). -/
def uzp (o : Nat) : VPermOp := if o = 0 then .uzp1 else .uzp2

theorem vbyte_uzp (o : Nat) (ho : o < 2) (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval (uzp o) .b16 x y) e =
      if e < 8 then vbyte x (2 * e + o) else vbyte y (2 * e + o - 16) := by
  rcases (by omega_arith : o = 0 ∨ o = 1) with rfl | rfl
  · exact vbyte_uzp1 x y he
  · exact vbyte_uzp2 x y he

/-- Word `k` of four vectors. -/
def four (W0 W1 W2 W3 : BitVec 128) (k : Nat) : BitVec 128 := [W0, W1, W2, W3].getD k 0

theorem uzp_uzp (W0 W1 W2 W3 : BitVec 128) {o₁ o₂ : Nat} (h₁ : o₁ < 2) (h₂ : o₂ < 2) {n : Nat}
    (hn : n < 16) :
    vbyte (VPermOp.eval (uzp o₂) .b16 (VPermOp.eval (uzp o₁) .b16 W0 W1)
        (VPermOp.eval (uzp o₁) .b16 W2 W3)) n =
      vbyte (four W0 W1 W2 W3 (n / 4)) (4 * (n % 4) + (o₁ + 2 * o₂)) := by
  rw [vbyte_uzp _ h₂ _ _ hn]
  split
  · rw [vbyte_uzp _ h₁ _ _ (by omega_arith)]
    split
    · rw [show n / 4 = 0 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show n / 4 = 1 by omega_arith]; exact congrArg _ (by omega_arith)
  · rw [vbyte_uzp _ h₁ _ _ (by omega_arith)]
    split
    · rw [show n / 4 = 2 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show n / 4 = 3 by omega_arith]; exact congrArg _ (by omega_arith)

/-- `zip1` (`o = 0`) or `zip2` (`o = 1`). -/
def zip (o : Nat) : VPermOp := if o = 0 then .zip1 else .zip2

theorem vbyte_zip (o : Nat) (ho : o < 2) (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval (zip o) .b16 x y) e =
      if e % 2 = 0 then vbyte x (8 * o + e / 2) else vbyte y (8 * o + e / 2) := by
  rcases (by omega_arith : o = 0 ∨ o = 1) with rfl | rfl
  · rw [show zip 0 = .zip1 from rfl, vbyte_zip1 x y he]; simp
  · exact vbyte_zip2 x y he

/-- Byte `b` of word `l` of `zip o₂ (zip o₁ P0 P2) (zip o₁ P1 P3)` is byte
`4 (2 o₁ + o₂) + l` of plane `b`: word `4 k + l` with `k = 2 o₁ + o₂`. -/
theorem zip_zip (P0 P1 P2 P3 : BitVec 128) {o₁ o₂ : Nat} (h₁ : o₁ < 2) (h₂ : o₂ < 2) {l b : Nat}
    (hl : l < 4) (hb : b < 4) :
    vbyte (VPermOp.eval (zip o₂) .b16 (VPermOp.eval (zip o₁) .b16 P0 P2)
        (VPermOp.eval (zip o₁) .b16 P1 P3)) (4 * l + b) =
      vbyte (four P0 P1 P2 P3 b) (4 * (2 * o₁ + o₂) + l) := by
  rw [vbyte_zip _ h₂ _ _ (by omega_arith)]
  split
  · rw [vbyte_zip _ h₁ _ _ (by omega_arith)]
    split
    · rw [show b = 0 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show b = 2 by omega_arith]; exact congrArg _ (by omega_arith)
  · rw [vbyte_zip _ h₁ _ _ (by omega_arith)]
    split
    · rw [show b = 1 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show b = 3 by omega_arith]; exact congrArg _ (by omega_arith)

end VG.Proof.Blowfish.AArch64
