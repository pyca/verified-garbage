module
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemMask

/-!
# The lanes of the blocks after the last group, as a group

In the masked group (`StitchZH.remG`), block `j` of the last `r` is lane
`j mod 4` of register `j / 4`, and each lane's products add up over the
registers in order: `laneAccG`, whose four lanes' reduced products add up to
`GHASH` over the `r` blocks for the powers of a group's table (`RemOkG`,
which `StitchZ/OkP.lean` proves, `remZG`). Lanes after the `r`
blocks are multiplied by zero, and add nothing (`laneAccG_pad`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB)
open VG.Spec.Gcm (Block ghashFrom)

/-- The products in lane `l` of the first `n` blocks `X` with their powers
`T`, block `j` in lane `j mod 4`, `y` added to the first. -/
def laneAccG (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (l : Nat) : Nat → Prod
  | 0 => Prod.zero
  | n + 1 => if n % 4 = l then (laneAccG X T y l n).acc ((if n = 0 then y else 0) ^^^ X n) (T n)
      else laneAccG X T y l n

theorem laneAccG_congr {X X' : Nat → Block} {T T' : Nat → BitVec 128} (y : Block) (l : Nat) :
    ∀ n, (∀ j < n, X j = X' j) → (∀ j < n, T j = T' j) → laneAccG X T y l n = laneAccG X' T' y l n
  | 0, _, _ => rfl
  | n + 1, hX, hT => by
    simp only [laneAccG]
    rw [laneAccG_congr y l n (fun j hj => hX j (by omega)) (fun j hj => hT j (by omega)), hX n (by omega),
      hT n (by omega)]

/-- The four blocks of register `q`, one to each lane. -/
theorem laneAccG_quad (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (q : Nat) {l : Nat} (hl : l < 4) :
    laneAccG X T y l (4 * q + 4) =
      (laneAccG X T y l (4 * q)).acc ((if 4 * q + l = 0 then y else 0) ^^^ X (4 * q + l)) (T (4 * q + l)) := by
  have h0 : (4 * q) % 4 = 0 := by omega
  have h1 : (4 * q + 1) % 4 = 1 := by omega
  have h2 : (4 * q + 2) % 4 = 2 := by omega
  have h3 : (4 * q + 3) % 4 = 3 := by omega
  rw [show 4 * q + 4 = 4 * q + 3 + 1 from rfl]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
  simp only [laneAccG, h0, h1, h2, h3, Nat.add_zero, ite_true, ite_false,
    show ¬ ((3 : Nat) = 0) by decide, show ¬ ((2 : Nat) = 0) by decide,
    show ¬ ((1 : Nat) = 0) by decide, show ¬ ((3 : Nat) = 1) by decide, show ¬ ((2 : Nat) = 1) by decide,
    show ¬ ((0 : Nat) = 1) by decide, show ¬ ((3 : Nat) = 2) by decide, show ¬ ((1 : Nat) = 2) by decide,
    show ¬ ((0 : Nat) = 2) by decide, show ¬ ((2 : Nat) = 3) by decide, show ¬ ((1 : Nat) = 3) by decide,
    show ¬ ((0 : Nat) = 3) by decide]

/-- Blocks multiplied by zero add nothing: past `r`, with powers zero there,
the lanes are those of the first `r`. -/
theorem laneAccG_pad (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (l r : Nat) :
    ∀ n, r ≤ n → laneAccG X (fun j => if j < r then T j else 0) y l n = laneAccG X T y l r
  | 0, h => by
    rw [show r = 0 by omega]; rfl
  | n + 1, h => by
    by_cases hn : n + 1 = r
    · subst hn
      exact laneAccG_congr y l (n + 1) (fun _ _ => rfl) fun j hj => by simp [hj]
    · have ih := laneAccG_pad X T y l r n (by omega)
      simp only [laneAccG]
      rw [ih, ite_eq_right (show ¬ n < r by omega)]
      split <;> [exact Prod.acc_zero_right _ _; rfl]

/-- What the products of the last `r` blocks with the powers of a group, in
the lanes of the masked group, add up to, each lane's reduced: `GHASH` over
the `r` blocks (`StitchZ/OkP.lean` proves it of the powers the setup stores,
`H'¹⁶⁻ᵐ` at `16 m`). -/
def RemOkG (H : Block) (P : Nat → Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 15 → ∀ (X : Nat → Block) (y : Block),
    (reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 0 r) ^^^
        reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 2 r)) ^^^
      (reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 1 r) ^^^
        reduceB (laneAccG X (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y 3 r)) =
      ghashFrom H y ((List.range r).map X)

end VG.Proof.Gcm.X86_64.StitchZH
