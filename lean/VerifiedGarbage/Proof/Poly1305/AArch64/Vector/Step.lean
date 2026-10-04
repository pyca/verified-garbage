import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Group
import VerifiedGarbage.Proof.Poly1305.Spec

/-!
# Poly1305 on AArch64 in AdvSIMD: a group, modulo `p`

Untrusted: everything here is checked by Lean. The lanes after a group, as
numbers modulo `p`: lane `e` is `m_(2+e) ρ_(2+e) + (H_e + m_e) ρ_e`, for the
blocks `m_j` at `x2 + 16 j` and the multipliers `ρ_c` (`val (y c)`).
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Spec.Poly1305 (P leNum bytesAt)

/-- Block `j` of a group, as bytes. -/
abbrev gbytes (s : State) (j : Nat) : List Byte := bytesAt s.mem (gAddr s j) 16

theorem gblk_val (s : State) (j : Nat) : val (gblk s j) = mv (gbytes s j) := by
  rw [gblk, blk_val (vdword _ 0).isLt (vdword _ 1).isLt, mv, Poly1305.leNum_append, Poly1305.length_bytesAt,
    Poly1305.leNum_bytesAt_16]
  simp only [vdword_read16 _ _ (show 0 < 2 by decide), vdword_read16 _ _ (show 1 < 2 by decide),
    Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  rfl

theorem val_add (a b : Nat → Nat) : val (fun i => a i + b i) = val a + val b := by
  simp only [val]; omega

theorem val_congr {a b : Nat → Nat} (h : ∀ i < 5, a i = b i) : val a = val b := by
  simp only [val, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem gprod_mod (H : Nat → Nat) (y : Nat → Nat → Nat) (b : Nat → Nat → Nat) (e : Nat) :
    val (gprod H y b e) ≡ val (b (2 + e)) * val (y (2 + e)) + (val H + val (b e)) * val (y e) [MOD P] := by
  have h : val (gprod H y b e) = val (Pair.prod (b (2 + e)) (y (2 + e))) +
      val (Pair.prod (fun i => H i + b e i) (y e)) := by
    simp only [val, gprod]; omega
  rw [h, ← val_add H (b e)]
  exact (Pair.prod_mod _ _).add (Pair.prod_mod _ _)

/-- Lane `e` after a group. -/
theorem group_lane {s t : State} {y : Nat → Nat → Nat} {e : Nat}
    (h : ∀ i < 5, hl t e i = Pair.carry (gprod (hl s e) y (gblk s) e) i) :
    val (hl t e) ≡ mv (gbytes s (2 + e)) * val (y (2 + e)) + (val (hl s e) + mv (gbytes s e)) * val (y e)
      [MOD P] := by
  rw [val_congr h, ← gblk_val, ← gblk_val]
  exact (Pair.carry_mod _).trans (gprod_mod _ _ _ _)

end VG.Proof.Poly1305.AArch64.Vector
