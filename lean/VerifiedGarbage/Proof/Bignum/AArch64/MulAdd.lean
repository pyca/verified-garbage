import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-!
# Multiword arithmetic on AArch64: a multiply-accumulate step

`mac down`: the word `x1 · y + c + x` (`y` at `x17`, `x` at `x16` or
`x16 + 8`, `c` in `x2`), whose low word is stored at `x16` and whose high
word is the new `x2`; both pointers advanced (`mac_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem add_ofNat0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem add_zero64 (x : BitVec 64) : x + (0 : BitVec 64) = x := BitVec.add_zero x

theorem zero_add64 (x : BitVec 64) : (0 : BitVec 64) + x = x := BitVec.zero_add x

/-- The value of a multiply-accumulate step: the product's low word plus two
words, with the product's high word plus the two carries. -/
theorem mac_val (a y c x : BitVec 64) :
    (a * y + c + x).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * y.toNat / 2 ^ 64) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (a * y).toNat + c.toNat)).toNat +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (a * y + c).toNat + x.toNat)).toNat).toNat =
      a.toNat * y.toNat + c.toNat + x.toNat := by
  have ha := a.isLt; have hy := y.isLt; have hc := c.isLt; have hx := x.isLt
  have hle : a.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  by_cases h1 : 2 ^ 64 ≤ (a * y).toNat + c.toNat <;>
  by_cases h2 : 2 ^ 64 ≤ (a * y + c).toNat + x.toNat <;>
  simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at h1 h2 ⊢ <;>
  generalize a.toNat * y.toNat = P at * <;>
  omega

/-- A multiply-accumulate step: `x1 · [x17] + x2 + [x16 + xo]` (`xo` 8 if
`down`, else 0), its low word stored at `x16`. -/
theorem mac_ok (s : State) (down : Bool) {B : Addr} {Z eD eS : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eD) (h17 : s.gpr .x17 = off B eS) (h7 : s.gpr .x7 = 0)
    (hS : eS + 8 ≤ Z) (hX : eD + (if down then 8 else 0) + 8 ≤ Z) (hD : eD + 8 ≤ Z) :
    WP isa (.block (mac down)) s fun t =>
      ∃ lo : BitVec 64, t.mem = s.mem.writeW (off B eD) lo ∧
        lo.toNat + 2 ^ 64 * (t.gpr .x2).toNat = (s.gpr .x1).toNat * (word s.mem B eS).toNat +
          (s.gpr .x2).toNat + (word s.mem B (eD + if down then 8 else 0)).toNat ∧
        t.gpr .x16 = off B (eD + 8) ∧ t.gpr .x17 = off B (eS + 8) := by
  cases down <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at hX ⊢ <;>
  · unfold mac
    brun [h16, h17, h7, hs.ld hS, hs.ld hX, hs.st hD]
    simp only [Bool.toNat_false, Nat.add_zero, add_ofNat0, add_zero64]
    exact ⟨_, rfl, mac_val _ _ _ _⟩

end VG.Proof.Bignum.AArch64
