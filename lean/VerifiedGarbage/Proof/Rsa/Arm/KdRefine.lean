module

public import VerifiedGarbage.Proof.Rsa.Arm.KdQuot
import VerifiedGarbage.Proof.Bignum.WordStepNorm32

/-! # The 3-by-2 refinement of the key checks' division on ARMv7 (`KeyDiv.refine3`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The part of `refine3` after its two products, up to the store. -/
def refineTail : List Instr :=
  [.adds .r1 .r3 (.reg .r10), .adc .r2 .r4 (.imm 0),
    .ldr .r10 .r12 sU0, .subs .r10 .r10 (.reg .r0), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
    .dp .eor .r3 .r3 (.imm 1),
    .subs .r11 .r11 (.reg .r1), .mov .r4 (.imm 1), .adc .r4 .r4 (.imm 0), .subs .r11 .r11 (.reg .r3),
    .adc .r4 .r4 (.imm 0), .dp .eor .r3 .r4 (.imm 3),
    .ldr .lr .r12 sU2, .dp .sub .lr .lr (.reg .r2), .dp .sub .lr .lr (.reg .r3), .ldr .r1 .r12 sQ] ++ fix3 ++ fix3

theorem negMask (t : BitVec 32) : (0 : BitVec 32) - t >>> 31 = if 2 ^ 31 ≤ t.toNat then -1 else 0 := by
  have e : (t >>> 31).toNat = t.toNat / 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := t.isLt
  by_cases h : 2 ^ 31 ≤ t.toNat
  · simp only [h, ↓reduceIte]
    have : t >>> 31 = 1 := BitVec.eq_of_toNat_eq (by rw [e]; show _ = 1; omega)
    rw [this]; decide
  · simp only [h, ↓reduceIte]
    have : t >>> 31 = 0 := BitVec.eq_of_toNat_eq (by rw [e]; show _ = 0; omega)
    rw [this]; decide

theorem and_negMask (x : BitVec 32) (c : Prop) [Decidable c] :
    (x &&& if c then (-1 : BitVec 32) else 0) = if c then x else 0 := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
  · simp only [h, ↓reduceIte]; exact BitVec.and_zero

theorem carry_toNat (a b : BitVec 32) :
    ((0 : BitVec 32) + 0 + bif decide (2 ^ 32 ≤ a.toNat + b.toNat) then 1 else 0).toNat =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp [h]

theorem carry_div (n : Nat) : (bif decide (2 ^ 32 ≤ n) then (1 : BitVec 32) else 0).toNat = min (n / 2 ^ 32) 1 := by
  by_cases h : 2 ^ 32 ≤ n
  · simp only [h, decide_true, Bool.cond_true]; show 1 = _; omega
  · simp only [h, decide_false, Bool.cond_false]; show 0 = _; omega

/-- `fix3`: for `t = (t₂, t₁, t₀)` negative (its top bit set), `q̂ - 1` and
`t + D` modulo `2^96`. -/
theorem fix3_ok {s : State} {B : BitVec 32} (h12 : s.gpr .r12 = B)
    {d d1 : BitVec 32} (hD : s.mem.readW (off (State.addr B) sD) 32 = d)
    (hD1 : s.mem.readW (off (State.addr B) sD1) 32 = d1)
    (aD : State.addr (B + BitVec.ofNat 32 sD) = off (State.addr B) sD)
    (aD1 : State.addr (B + BitVec.ofNat 32 sD1) = off (State.addr B) sD1)
    (rD : InRegions (s.rd ++ s.wr) (off (State.addr B) sD) 4)
    (rD1 : InRegions (s.rd ++ s.wr) (off (State.addr B) sD1) 4) :
    WP isa (.block fix3) s fun t =>
      t.gpr .r1 = s.gpr .r1 + (if 2 ^ 31 ≤ (s.gpr .lr).toNat then -1 else 0) ∧
      (t.gpr .r10).toNat + (t.gpr .r11).toNat * 2 ^ 32 + (t.gpr .lr).toNat * 2 ^ 64 =
        ((s.gpr .r10).toNat + (s.gpr .r11).toNat * 2 ^ 32 + (s.gpr .lr).toNat * 2 ^ 64 +
          if 2 ^ 31 ≤ (s.gpr .lr).toNat then d.toNat * 2 ^ 32 + d1.toNat else 0) % 2 ^ 96 ∧
      t.mem = s.mem ∧ t.gpr .r12 = s.gpr .r12 := by
  krun [fix3, h12, hD, hD1, aD, aD1, rD, rD1]
  simp only [negMask, and_negMask]
  by_cases hn : 2 ^ 31 ≤ (s.gpr .lr).toNat
  · simp only [hn, ↓reduceIte, true_and]
    simp only [BitVec.toNat_add]
    simp only [carry_div, show BitVec.toNat (0 : BitVec 32) = 0 from rfl, Nat.zero_add, Nat.zero_mod,
      Nat.add_zero]
    omega
  · simp only [hn, ↓reduceIte, true_and]
    have z0 : BitVec.toNat (0 : BitVec 32) = 0 := rfl
    have nc : ∀ x : BitVec 32, decide (2 ^ 32 ≤ x.toNat + 0) = false := fun x => by
      have := x.isLt; simp only [decide_eq_false_iff_not]; omega
    rw [z0, nc, nc]
    have e0 : (0 + 0 + bif false then (1 : BitVec 32) else 0) = 0 := by decide
    have a0 : ∀ x : BitVec 32, x + 0 = x := fun x => BitVec.add_zero x
    rw [e0, a0, a0, z0, nc, e0, a0, e0, a0]
    have h0 := (s.gpr .r10).isLt
    have h1 := (s.gpr .r11).isLt
    have h2 := (s.gpr .lr).isLt
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Rsa.Arm.KeyDiv
