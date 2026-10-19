module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Xts

import VerifiedGarbage.Proof.AesXts.Alpha
import Mathlib.Data.List.Induction

/-!
# XTS: sixteen multiplications by `α` at once

Untrusted: everything here is checked by Lean. A tweak as a 128-bit
little-endian word `v` (its bytes are `b16 v`) times `α` is `mulA128 v`: `v`
shifted left by one, and `0x87` XORed in if its top bit was set
(`mulAlpha_b16`). Sixteen of them at once are `v` shifted left by sixteen,
XORed with `P (v >>> 112)`, where `P c = c ⊕ c ≪ 1 ⊕ c ≪ 2 ⊕ c ≪ 7` is the
carry-less product of `c` and `0x87` (`repeat_mulA128`, `next_b16`); eight
are `v` shifted left by eight, XORed with `P (v >>> 120)` (`next_b8`).
-/

@[expose] public section

namespace VG.Proof.AesXts

open VG
open VG.Spec.Xts (mulAlpha)

/-- The bytes of a 128-bit word, the least significant first. -/
def b16 (v : BitVec 128) : List Byte := (List.range 16).map fun j => v.extractLsb' (8 * j) 8

/-- The tweak `v` times `α`. -/
def mulA128 (v : BitVec 128) : BitVec 128 := (v <<< 1) ^^^ (if v.msb then (0x87 : BitVec 128) else 0)

theorem mulAlpha_b16 (v : BitVec 128) : b16 (mulA128 v) = mulAlpha (b16 v) := by
  simp only [b16, mulA128, List.range, List.range.loop, List.map]
  rw [mulAlpha_16, msb_byte v 15 rfl]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [byte_shl_xor _ _ (by decide)]; rfl

/-- The carry-less product of `c` and `0x87`. -/
def P (c : BitVec 128) : BitVec 128 := c ^^^ (c <<< 1) ^^^ (c <<< 2) ^^^ (c <<< 7)

theorem P_xor (a b : BitVec 128) : P (a ^^^ b) = P a ^^^ P b := by
  simp only [P, BitVec.shiftLeft_xor_distrib]; ac_rfl

theorem P_shl (c : BitVec 128) (k : Nat) : P (c <<< k) = P c <<< k := by
  simp only [P, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add, Nat.add_comm k]

theorem P_bit (b : Bool) : P (if b then 1 else 0) = if b then (0x87 : BitVec 128) else 0 := by
  cases b <;> rfl

theorem P_zero : P 0#128 = 0#128 := rfl

/-- The top bit after `k ≤ 120` multiplications by `α`. -/
theorem msb_step (v : BitVec 128) {k : Nat} (hk : k ≤ 120) :
    ((v <<< k) ^^^ P (v >>> (128 - k))).msb = v.getLsbD (127 - k) := by
  simp only [BitVec.msb_eq_getLsbD_last, P, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  have h1 : ¬ (128 - k + (127 - 1) < 128) := by omega
  have h2 : ¬ (128 - k + (127 - 2) < 128) := by omega
  have h7 : ¬ (128 - k + (127 - 7) < 128) := by omega
  have h0 : ¬ (128 - k + 127 < 128) := by omega
  simp [BitVec.getLsbD_of_ge, show 128 - k + 127 ≥ 128 by omega, show 128 - k + 126 ≥ 128 by omega,
    show 128 - k + 125 ≥ 128 by omega, show 128 - k + 120 ≥ 128 by omega]
  omega

/-- The bits shifted out after `k + 1` multiplications, from those after
`k`. -/
theorem shr_step (v : BitVec 128) {k : Nat} (hk : k < 128) :
    v >>> (128 - (k + 1)) = ((v >>> (128 - k)) <<< 1) ^^^ (if v.getLsbD (127 - k) then 1 else 0) := by
  ext i hi
  by_cases h0 : i = 0
  · subst h0
    cases hb : v.getLsbD (127 - k) <;> simp [hb, show 128 - (k + 1) = 127 - k by omega]
  · cases hb : v.getLsbD (127 - k) <;>
      simp [BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft, h0, show ¬ i < 1 by omega] <;>
      (congr 1; omega)

/-- `k ≤ 120` multiplications by `α`. -/
theorem repeat_mulA128 (v : BitVec 128) : ∀ k, k ≤ 120 →
    Nat.repeat mulA128 k v = (v <<< k) ^^^ P (v >>> (128 - k))
  | 0, _ => by
    simp only [Nat.repeat, BitVec.shiftLeft_zero, Nat.sub_zero, BitVec.ushiftRight_eq_zero (Nat.le_refl 128)]
    rw [show P 0#128 = 0#128 from rfl, BitVec.xor_zero]
  | k + 1, hk => by
    rw [Nat.repeat, repeat_mulA128 v k (by omega), mulA128, msb_step v (by omega), shr_step v (by omega), P_xor,
      P_bit, BitVec.shiftLeft_xor_distrib, P_shl, ← BitVec.shiftLeft_add]
    ac_rfl

theorem repeat_mulAlpha_b16 (v : BitVec 128) (k : Nat) :
    Nat.repeat mulAlpha k (b16 v) = b16 (Nat.repeat mulA128 k v) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.repeat, ih, Nat.repeat, mulAlpha_b16]

/-- The tweak eight blocks on. -/
theorem next_b8 (v : BitVec 128) : Spec.Xts.next (b16 v) 8 = b16 ((v <<< 8) ^^^ P (v >>> 120)) := by
  rw [Spec.Xts.next, repeat_mulAlpha_b16, repeat_mulA128 v 8 (by decide)]

/-- The tweak sixteen blocks on. -/
theorem next_b16 (v : BitVec 128) : Spec.Xts.next (b16 v) 16 = b16 ((v <<< 16) ^^^ P (v >>> 112)) := by
  rw [Spec.Xts.next, repeat_mulAlpha_b16, repeat_mulA128 v 16 (by decide)]

end VG.Proof.AesXts
