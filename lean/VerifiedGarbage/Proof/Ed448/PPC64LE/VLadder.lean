module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.VTab
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseStep
public import VerifiedGarbage.Proof.Ed448.Ref

/-!
# Ed448's verification on PPC64LE: the ladder's points

The point `Q` holds while the loop's counter is `c` (`Qv`): the iterations
`h ≥ c` are done, those of the bits above `c / 4` and of bit `c / 4` the
phases from 3 down to `c % 4` (`vphase`). One iteration (`qv_step`) adds the
selected point `P` (`Q`, `B`, `a` or `r` by the two bits of `h = c - 1`) and
keeps the sum by the mask `TAB[h]` (`tabV`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG.Spec.Ed448 (Point pointAdd basePoint)
open VG.Proof.Ed448 (vladder4 vstep4 vphase vbit vladder4_bit bitAt)

/-- The point in `Q` while the counter is `c`, for the scalars `S`, `K` and `4`. -/
def Qv (S K : Nat) (a r : Point) (c : Nat) : Point :=
  if c % 4 = 0 then vladder4 S K 4 a r (458 - c / 4)
  else if c % 4 = 3 then vphase 3 true a r (vladder4 S K 4 a r (458 - (c / 4 + 1)))
  else if c % 4 = 2 then vphase 2 (vbit S K 4 2 (c / 4)) a r
    (vphase 3 true a r (vladder4 S K 4 a r (458 - (c / 4 + 1))))
  else vphase 1 (vbit S K 4 1 (c / 4)) a r (vphase 2 (vbit S K 4 2 (c / 4)) a r
    (vphase 3 true a r (vladder4 S K 4 a r (458 - (c / 4 + 1)))))

theorem qv_1832 (S K : Nat) (a r : Point) : Qv S K a r 1832 = Spec.Ed448.identity := by
  simp only [Qv, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, ↓reduceIte]; rfl

theorem qv_0 (S K : Nat) (a r : Point) : Qv S K a r 0 = vladder4 S K 4 a r 458 := by
  simp only [Qv, Nat.zero_mod, Nat.zero_div, Nat.sub_zero, ↓reduceIte]

/-- The selected point of the iteration `h`: `Q` for `h % 4 = 3`, `B`, `a`
and `r` for 2, 1 and 0. -/
def selP (h : Nat) (a r q : Point) : Point := pick (h / 2 % 2) (pick (h % 2) r a) (pick (h % 2) basePoint q)

theorem pick_bit {α : Type} {β : Nat} (hβ : β ≤ 1) (x y : α) :
    pick β x y = if decide (β = 1) then y else x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hβ with rfl | rfl <;> rfl

theorem tabV_le (S K h : Nat) : tabV S K h ≤ 1 := by
  unfold tabV
  split
  · exact Nat.le_refl _
  · split
    · rw [Nat.and_one_is_mod]; omega
    · split <;> (rw [Nat.and_one_is_mod]; omega)

/-- One iteration. -/
theorem qv_step (S K : Nat) (a r : Point) {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 1832) :
    pick (tabV S K (c - 1)) (Qv (4 * S) (4 * K) a r c)
      (pointAdd (Qv (4 * S) (4 * K) a r c) (selP (c - 1) a r (Qv (4 * S) (4 * K) a r c))) =
      Qv (4 * S) (4 * K) a r (c - 1) := by
  have hb := tabV_le S K (c - 1)
  rw [pick_bit hb]
  rcases (by omega : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3) with r0 | r1 | r2 | r3
  · -- `h % 4 = 3`: a doubling.
    have e1 : (c - 1) % 4 = 3 := by omega
    have e2 : (c - 1) / 4 + 1 = c / 4 := by omega
    simp only [Qv, r0, e1, e2, selP, tabV, show (c - 1) % 2 = 1 by omega, show (c - 1) / 2 % 2 = 1 by omega,
      pick, X25519.PPC64LE.sel, Nat.reduceEqDiff, ↓reduceIte, decide_true]
    rfl
  · -- `h % 4 = 0`: `r`, and the bit's last iteration.
    have e1 : (c - 1) % 4 = 0 := by omega
    have e2 : (c - 1) / 4 = c / 4 := by omega
    have ht : c / 4 < 458 := by omega
    simp only [Qv, r1, e1, e2, selP, tabV, show (c - 1) % 2 = 0 by omega, show (c - 1) / 2 % 2 = 0 by omega,
      pick, X25519.PPC64LE.sel, Nat.reduceEqDiff, ↓reduceIte]
    rw [show 458 - c / 4 = 458 - c / 4 from rfl, vladder4_bit _ _ _ _ _ ht]
    simp only [vstep4, vphase, vbit, bitAt, Nat.reduceEqDiff, ↓reduceIte]
  · -- `h % 4 = 1`: `a`.
    have e1 : (c - 1) % 4 = 1 := by omega
    have e2 : (c - 1) / 4 = c / 4 := by omega
    simp only [Qv, r2, e1, e2, selP, tabV, show (c - 1) % 2 = 1 by omega, show (c - 1) / 2 % 2 = 0 by omega,
      pick, X25519.PPC64LE.sel, Nat.reduceEqDiff, ↓reduceIte]
    simp only [vphase, vbit, bitAt, Nat.reduceEqDiff, ↓reduceIte]
  · -- `h % 4 = 2`: `B`.
    have e1 : (c - 1) % 4 = 2 := by omega
    have e2 : (c - 1) / 4 = c / 4 := by omega
    simp only [Qv, r3, e1, e2, selP, tabV, show (c - 1) % 2 = 0 by omega, show (c - 1) / 2 % 2 = 1 by omega,
      pick, X25519.PPC64LE.sel, Nat.reduceEqDiff, ↓reduceIte]
    simp only [vphase, vbit, bitAt, Nat.reduceEqDiff, ↓reduceIte]

end VG.Proof.Ed448.PPC64LE
