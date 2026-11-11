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

theorem geBit (a b : Nat) : (bif decide (a ≤ b) then (1 : BitVec 32) else 0).toNat = min (b + 1 - a) 1 := by
  by_cases h : a ≤ b
  · simp only [h, decide_true, Bool.cond_true]; show 1 = _; omega
  · simp only [h, decide_false, Bool.cond_false]; show 0 = _; omega

theorem geBit_xor1 (a b : Nat) :
    ((0 + 0 + bif decide (a ≤ b) then (1 : BitVec 32) else 0) ^^^ 1).toNat = 1 - min (b + 1 - a) 1 := by
  by_cases h : a ≤ b
  · simp only [h, decide_true, Bool.cond_true]; show 0 = _; omega
  · simp only [h, decide_false, Bool.cond_false]; show 1 = _; omega

theorem geBits_xor3 (a b c d : Nat) :
    (((1 + 0 + bif decide (a ≤ b) then (1 : BitVec 32) else 0) + 0 + bif decide (c ≤ d) then 1 else 0) ^^^
      3).toNat = 2 - min (b + 1 - a) 1 - min (d + 1 - c) 1 := by
  by_cases h : a ≤ b <;> by_cases h' : c ≤ d <;>
    simp only [h, h', decide_true, decide_false, Bool.cond_true, Bool.cond_false] <;>
    first | (show 0 = _; omega) | (show 1 = _; omega) | (show 2 = _; omega)

/-- `sub96`'s arithmetic: `U - q̂ D` modulo `2^96`, by words with their borrows. -/
theorem sub96_nat {r0 r3 r4 r10 r11 u0 u2 : Nat} (h0 : r0 < 2 ^ 32) (h3 : r3 < 2 ^ 32) (h4 : r4 < 2 ^ 32)
    (h10 : r10 < 2 ^ 32) (h11 : r11 < 2 ^ 32) (hu0 : u0 < 2 ^ 32) (hu2 : u2 < 2 ^ 32)
    (hq : r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64 < 2 ^ 96) :
    (2 ^ 32 - r0 + u0) % 2 ^ 32 +
        (2 ^ 32 - (1 - min (u0 + 1 - r0) 1) + (2 ^ 32 - (r3 + r10) % 2 ^ 32 + r11) % 2 ^ 32) % 2 ^ 32 * 2 ^ 32 +
      (2 ^ 32 - (2 - min (r11 + 1 - (r3 + r10) % 2 ^ 32) 1 -
            min ((2 ^ 32 - (r3 + r10) % 2 ^ 32 + r11) % 2 ^ 32 + 1 - (1 - min (u0 + 1 - r0) 1)) 1) +
          (2 ^ 32 - (r4 % 2 ^ 32 + min (r3 + r10 + 1 - 2 ^ 32) 1) % 2 ^ 32 + u2) % 2 ^ 32) % 2 ^ 32 * 2 ^ 64 =
      (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64)) % 2 ^ 96 := by
  have e1 := Nat.div_add_mod (r3 + r10) (2 ^ 32)
  have b1 : (r3 + r10) / 2 ^ 32 < 2 := by omega
  have b2 := Nat.mod_lt (r3 + r10) (Nat.two_pow_pos 32)
  have e2 : min (r3 + r10 + 1 - 2 ^ 32) 1 = (r3 + r10) / 2 ^ 32 := by omega
  rw [e2, Nat.mod_eq_of_lt h4]
  generalize (r3 + r10) % 2 ^ 32 = m at *
  generalize (r3 + r10) / 2 ^ 32 = c at *
  have e3 : (r4 + c) % 2 ^ 32 = r4 + c := Nat.mod_eq_of_lt (by omega)
  rw [e3]
  have b0 : 1 - min (u0 + 1 - r0) 1 = if r0 ≤ u0 then 0 else 1 := by split <;> omega
  have bm : 2 - min (r11 + 1 - m) 1 - min ((2 ^ 32 - m + r11) % 2 ^ 32 + 1 - (if r0 ≤ u0 then 0 else 1)) 1 =
      (if m ≤ r11 then 0 else 1) + (if (if r0 ≤ u0 then 0 else 1) ≤ (2 ^ 32 - m + r11) % 2 ^ 32 then 0 else 1) := by
    repeat' split
    all_goals omega
  rw [b0, bm]
  -- t0
  have f0 : u0 + (if r0 ≤ u0 then 0 else 1) * 2 ^ 32 = r0 + (2 ^ 32 - r0 + u0) % 2 ^ 32 := by split <;> omega
  have g0 := Nat.mod_lt (2 ^ 32 - r0 + u0) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - r0 + u0) % 2 ^ 32 = t0 at *
  generalize (if r0 ≤ u0 then 0 else 1) = x0 at *
  have hx0 : x0 < 2 := by omega
  -- a
  have fa : r11 + (if m ≤ r11 then 0 else 1) * 2 ^ 32 = m + (2 ^ 32 - m + r11) % 2 ^ 32 := by split <;> omega
  have ga := Nat.mod_lt (2 ^ 32 - m + r11) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - m + r11) % 2 ^ 32 = a at *
  generalize (if m ≤ r11 then 0 else 1) = xa at *
  have hxa : xa < 2 := by omega
  -- t1
  have f1 : a + (if x0 ≤ a then 0 else 1) * 2 ^ 32 = x0 + (2 ^ 32 - x0 + a) % 2 ^ 32 := by split <;> omega
  have g1 := Nat.mod_lt (2 ^ 32 - x0 + a) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - x0 + a) % 2 ^ 32 = t1 at *
  generalize (if x0 ≤ a then 0 else 1) = xb at *
  have hxb : xb < 2 := by omega
  -- t2
  have f2 := Nat.div_add_mod (2 ^ 32 - (r4 + c) + u2) (2 ^ 32)
  have g2 := Nat.mod_lt (2 ^ 32 - (r4 + c) + u2) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - (r4 + c) + u2) % 2 ^ 32 = y at *
  have f3 := Nat.div_add_mod (2 ^ 32 - (xa + xb) + y) (2 ^ 32)
  have g3 := Nat.mod_lt (2 ^ 32 - (xa + xb) + y) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - (xa + xb) + y) % 2 ^ 32 = t2 at *
  have f4 := Nat.div_add_mod (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64)) (2 ^ 96)
  have g4 := Nat.mod_lt (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64))
    (Nat.two_pow_pos 96)
  generalize (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64)) % 2 ^ 96 = z at *
  omega

/-- The subtraction of `quot3`, after its two products. -/
def sub96 : List Instr :=
  [.adds .r1 .r3 (.reg .r10), .adc .r2 .r4 (.imm 0),
    .ldr .r10 .r12 sU0, .subs .r10 .r10 (.reg .r0), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
    .dp .eor .r3 .r3 (.imm 1),
    .subs .r11 .r11 (.reg .r1), .mov .r4 (.imm 1), .adc .r4 .r4 (.imm 0), .subs .r11 .r11 (.reg .r3),
    .adc .r4 .r4 (.imm 0), .dp .eor .r3 .r4 (.imm 3),
    .ldr .lr .r12 sU2, .dp .sub .lr .lr (.reg .r2), .dp .sub .lr .lr (.reg .r3)]

theorem sub96_ok {s : State} {B : BitVec 32} (h12 : s.gpr .r12 = B) {u0 u2 : BitVec 32}
    (hU0 : s.mem.readW (off (State.addr B) sU0) 32 = u0) (hU2 : s.mem.readW (off (State.addr B) sU2) 32 = u2)
    (aU0 : State.addr (B + BitVec.ofNat 32 sU0) = off (State.addr B) sU0)
    (aU2 : State.addr (B + BitVec.ofNat 32 sU2) = off (State.addr B) sU2)
    (rU0 : InRegions (s.rd ++ s.wr) (off (State.addr B) sU0) 4)
    (rU2 : InRegions (s.rd ++ s.wr) (off (State.addr B) sU2) 4)
    (hq : (s.gpr .r0).toNat + ((s.gpr .r3).toNat + (s.gpr .r10).toNat) * 2 ^ 32 + (s.gpr .r4).toNat * 2 ^ 64 <
      2 ^ 96) :
    WP isa (.block sub96) s fun t =>
      (t.gpr .r10).toNat + (t.gpr .r11).toNat * 2 ^ 32 + (t.gpr .lr).toNat * 2 ^ 64 =
        (u0.toNat + (s.gpr .r11).toNat * 2 ^ 32 + u2.toNat * 2 ^ 64 + 2 ^ 96 -
          ((s.gpr .r0).toNat + ((s.gpr .r3).toNat + (s.gpr .r10).toNat) * 2 ^ 32 + (s.gpr .r4).toNat * 2 ^ 64)) %
          2 ^ 96 ∧ t.mem = s.mem ∧ t.gpr .r12 = s.gpr .r12 := by
  krun [sub96, h12, hU0, hU2, aU0, aU2, rU0, rU2]
  simp only [geBits_xor3, geBit_xor1, BitVec.toNat_add, BitVec.toNat_sub, geBit,
    show BitVec.toNat (0 : BitVec 32) = 0 from rfl, Nat.add_zero]
  exact sub96_nat (s.gpr .r0).isLt (s.gpr .r3).isLt (s.gpr .r4).isLt (s.gpr .r10).isLt (s.gpr .r11).isLt
    u0.isLt u2.isLt hq

end VG.Proof.Rsa.Arm.KeyDiv
