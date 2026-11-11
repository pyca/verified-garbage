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

/-- `refine3`'s arithmetic: the two corrections take `q̂` to `Q` (`WordStep32.quot3_val`). -/
theorem refine3_math {U D q0 T1 T2 : Nat} (hD0 : 0 < D) (hDW : 4 * D < 2 ^ 96 / 2) (hUD : U < (2 ^ 32 + 1) * D)
    (hge : min (U / D) (2 ^ 32 - 1) ≤ q0) (hle : q0 ≤ min (U / D) (2 ^ 32 - 1) + 2) (hq0 : q0 < 2 ^ 32)
    (hU : U < 2 ^ 96) (hqD : q0 * D < 2 ^ 96)
    (hT1 : T1 = (U + 2 ^ 96 - q0 * D) % 2 ^ 96)
    (hT2 : T2 = (T1 + if 2 ^ 95 ≤ T1 then D else 0) % 2 ^ 96) :
    (q0 + (if 2 ^ 95 ≤ T1 then 2 ^ 32 - 1 else 0) + (if 2 ^ 95 ≤ T2 then 2 ^ 32 - 1 else 0)) % 2 ^ 32 =
      min (U / D) (2 ^ 32 - 1) := by
  have hT1' : T1 < 2 ^ 96 := hT1 ▸ Nat.mod_lt _ (Nat.two_pow_pos 96)
  have hT2' : T2 < 2 ^ 96 := hT2 ▸ Nat.mod_lt _ (Nat.two_pow_pos 96)
  have e1 : T1 + q0 * D = U + 2 ^ 96 * (if q0 * D ≤ U then 0 else 1) := by
    rw [hT1]; split <;> omega
  have e2 : T2 + 2 ^ 96 * ((T1 + if 2 ^ 95 ≤ T1 then D else 0) / 2 ^ 96) = T1 + if 2 ^ 96 / 2 ≤ T1 then D else 0 := by
    rw [hT2, show (2 : Nat) ^ 96 / 2 = 2 ^ 95 by decide]; omega
  have hv := VG.Proof.Bignum.WordStep32.quot3_val (W := 2 ^ 96) (T1 := T1) (T2 := T2) hD0 hDW hUD hge hle hq0
    hT1' (by split <;> decide) e1 hT2' (by split <;> omega) e2
  rw [show (2 : Nat) ^ 96 / 2 = 2 ^ 95 by decide] at hv
  have hQ : min (U / D) (2 ^ 32 - 1) < 2 ^ 32 := by omega
  rw [hv]
  generalize min (U / D) (2 ^ 32 - 1) = Q at hQ ⊢
  by_cases a1 : 2 ^ 95 ≤ T1 <;> by_cases a2 : 2 ^ 95 ≤ T2 <;> simp only [a1, a2, ↓reduceIte] <;> omega

theorem quot3_split : quot3 = ([.ldr .r1 .r12 sQ, .ldr .r2 .r12 sD1] : List Instr) ++
    (VG.Impl.Bignum.Arm.wideMul ++ (([.mov .r0 (.reg .r3), .mov .r10 (.reg .r4), .ldr .r1 .r12 sQ,
      .ldr .r2 .r12 sD] : List Instr) ++ (VG.Impl.Bignum.Arm.wideMul ++ sub96))) := by
  simp only [quot3, sub96, List.append_assoc]

theorem top_bit_iff {a b c : BitVec 32} :
    2 ^ 31 ≤ c.toNat ↔ 2 ^ 95 ≤ a.toNat + b.toNat * 2 ^ 32 + c.toNat * 2 ^ 64 := by
  have := a.isLt; have := b.isLt; have := c.isLt; omega

theorem negOne_toNat (q : BitVec 32) (c : Prop) [Decidable c] :
    (q + if c then (-1 : BitVec 32) else 0).toNat = (q.toNat + if c then 2 ^ 32 - 1 else 0) % 2 ^ 32 := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; rw [BitVec.toNat_add, show (-1 : BitVec 32).toNat = 2 ^ 32 - 1 by decide]
  · simp only [h, ↓reduceIte]; rw [BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl]

/-- The registers `refine3` changes. -/
abbrev refineRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- `refine3`: `q̂` (156), within `Q ≤ q̂ ≤ Q + 2` of `Q = min(⌊U / D⌋, 2^32 - 1)`, refined to
`Q`, for `U = (u₂, u₁, u₀)` (68, `r11`, 64) and `D = (d, d₁)` (140, 148), `U < (2^32 + 1) D`. -/
theorem refine3_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) (h12 : s.gpr .r12 = B)
    {q0 u1 : Nat} (hu1 : s.gpr .r11 = BitVec.ofNat 32 u1) (hu1' : u1 < 2 ^ 32) (hQ0 : slot s.mem B sQ = q0)
    {U D : Nat} (hU : U = slot s.mem B sU2 * 2 ^ 64 + u1 * 2 ^ 32 + slot s.mem B sU0)
    (hD : D = slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1) (hD0 : 0 < D) (hUD : U < (2 ^ 32 + 1) * D)
    (hge : min (U / D) (2 ^ 32 - 1) ≤ q0) (hle : q0 ≤ min (U / D) (2 ^ 32 - 1) + 2) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, slot t.mem B sQ = min (U / D) (2 ^ 32 - 1) → Keep B w [] [sQ] s.mem t.mem → t.gpr .r12 = B →
      Rest refineRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (refine3 ++ rest)) s Q := by
  have hz := h.hdr_le
  have sl : ∀ {o : Nat}, o + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → State.addr (B + BitVec.ofNat 32 o) = off (State.addr B) o ∧
      InRegions (s.rd ++ s.wr) (off (State.addr B) o) 4 ∧ InRegions s.wr (off (State.addr B) o) 4 := fun ho =>
    ⟨h.addr (by omega), h.read (by omega), h.write (by omega)⟩
  obtain ⟨aQ, rQ, wQ⟩ := sl (o := sQ) (by decide)
  obtain ⟨aD, rD, -⟩ := sl (o := sD) (by decide)
  obtain ⟨aD1, rD1, -⟩ := sl (o := sD1) (by decide)
  obtain ⟨aU0, rU0, -⟩ := sl (o := sU0) (by decide)
  obtain ⟨aU2, rU2, -⟩ := sl (o := sU2) (by decide)
  have tv : ∀ {o v : Nat}, slot s.mem B o = v → s.mem.readW (off (State.addr B) o) 32 = BitVec.ofNat 32 v :=
    fun e => by rw [← e]; exact (ofNat_toNat32 _).symm
  generalize ed : slot s.mem B sD = d at hD
  generalize ed1 : slot s.mem B sD1 = d1 at hD
  have hq0 : q0 < 2 ^ 32 := hQ0 ▸ BitVec.isLt _
  have hd : d < 2 ^ 32 := ed ▸ BitVec.isLt _
  have hd1 : d1 < 2 ^ 32 := ed1 ▸ BitVec.isLt _
  have tn : ∀ {a : Nat}, a < 2 ^ 32 → (BitVec.ofNat 32 a).toNat = a := fun h => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  simp only [refine3, quot3_split, List.append_assoc]
  -- `q̂ d₁`.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r1, .r2] (Q := fun v =>
      v.gpr .r1 = BitVec.ofNat 32 q0 ∧ v.gpr .r2 = BitVec.ofNat 32 d1 ∧ v.mem = s.mem) (by
    krun [h12, aQ, aD1, rQ, rD1, tv hQ0, tv ed1]) (by decide)) fun v1 ⟨⟨i1, p1, m1⟩, k1⟩ => ?_)
  refine wp_wide fun v2 e2 P2 => ?_
  rw [i1, p1, tn hq0, tn hd1] at e2
  -- `q̂ d`.
  have q12 : v2.gpr .r12 = B := (P2.regs _ (by decide)).trans ((k1.gpr _ (by decide)).trans h12)
  have m2 : v2.mem = s.mem := P2.mem.trans m1
  have rd2 : v2.rd = s.rd := P2.rd.trans k1.rd
  have wr2 : v2.wr = s.wr := P2.wr.trans k1.wr
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r10, .r1, .r2] (Q := fun v =>
      v.gpr .r0 = v2.gpr .r3 ∧ v.gpr .r10 = v2.gpr .r4 ∧ v.gpr .r1 = BitVec.ofNat 32 q0 ∧
      v.gpr .r2 = BitVec.ofNat 32 d ∧ v.mem = s.mem) (by
    krun [q12, m2, rd2, wr2, aQ, aD, rQ, rD, tv hQ0, tv ed]) (by decide)) fun v3 ⟨⟨x3, t3, i3, p3, m3⟩, k3⟩ => ?_)
  refine wp_wide fun v4 e4 P4 => ?_
  rw [i3, p3, tn hq0, tn hd] at e4
  -- `U - q̂ D`.
  have q12' : v4.gpr .r12 = B := (P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans q12)
  have m4 : v4.mem = s.mem := P4.mem.trans m3
  have rd4 : v4.rd = s.rd := P4.rd.trans (k3.rd.trans rd2)
  have wr4 : v4.wr = s.wr := P4.wr.trans (k3.wr.trans wr2)
  have x4 : v4.gpr .r0 = v2.gpr .r3 := (P4.regs _ (by decide)).trans x3
  have t4 : v4.gpr .r10 = v2.gpr .r4 := (P4.regs _ (by decide)).trans t3
  have u4 : v4.gpr .r11 = BitVec.ofNat 32 u1 :=
    (P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans ((P2.regs _ (by decide)).trans
      ((k1.gpr _ (by decide)).trans hu1)))
  have hqD : (v4.gpr .r0).toNat + ((v4.gpr .r3).toNat + (v4.gpr .r10).toNat) * 2 ^ 32 +
      (v4.gpr .r4).toNat * 2 ^ 64 = q0 * D := by
    rw [x4, t4, hD, Nat.mul_add, ← Nat.mul_assoc]; omega
  have hDlt : D < 2 ^ 64 := by rw [hD]; omega
  have hqD' : q0 * D < 2 ^ 96 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hq0 (Nat.le_of_lt hDlt) (by omega)) (by decide)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10, .r11, .lr]
    (sub96_ok q12' (u0 := BitVec.ofNat 32 (slot s.mem B sU0)) (u2 := BitVec.ofNat 32 (slot s.mem B sU2))
      (by rw [m4]; exact tv rfl) (by rw [m4]; exact tv rfl) aU0 aU2 (by rw [rd4, wr4]; exact rU0)
      (by rw [rd4, wr4]; exact rU2) (by rw [hqD]; exact hqD')) (by decide)) fun v5 ⟨⟨T5, m5, b5⟩, k5⟩ => ?_)
  rw [hqD, u4, tn hu1'] at T5
  have q12'' : v5.gpr .r12 = B := b5.trans q12'
  have m5' : v5.mem = s.mem := m5.trans m4
  have rd5 : v5.rd = s.rd := k5.rd.trans rd4
  have wr5 : v5.wr = s.wr := k5.wr.trans wr4
  -- `q̂` again, and the two corrections.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r1] (Q := fun v =>
      v.gpr .r1 = BitVec.ofNat 32 q0 ∧ v.mem = s.mem) (by
    krun [q12'', m5', rd5, wr5, aQ, rQ, tv hQ0]) (by decide)) fun v6 ⟨⟨i6, m6⟩, k6⟩ => ?_)
  have b6 : v6.gpr .r12 = B := (k6.gpr _ (by decide)).trans q12''
  have rd6 : v6.rd = s.rd := k6.rd.trans rd5
  have wr6 : v6.wr = s.wr := k6.wr.trans wr5
  have T6 : (v6.gpr .r10).toNat + (v6.gpr .r11).toNat * 2 ^ 32 + (v6.gpr .lr).toNat * 2 ^ 64 =
      (U + 2 ^ 96 - q0 * D) % 2 ^ 96 := by
    rw [k6.gpr .r10 (by decide), k6.gpr .r11 (by decide), k6.gpr .lr (by decide), T5, hU]
    congr 2
    simp only [BitVec.toNat_ofNat, slot]
    have := (s.mem.readW (off (State.addr B) sU0) 32).isLt
    have := (s.mem.readW (off (State.addr B) sU2) 32).isLt
    simp only [w32] at *
    omega
  have vD : v6.mem.readW (off (State.addr B) sD) 32 = BitVec.ofNat 32 d := by rw [m6]; exact tv ed
  have vD1 : v6.mem.readW (off (State.addr B) sD1) 32 = BitVec.ofNat 32 d1 := by rw [m6]; exact tv ed1
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10, .r11, .lr]
    (fix3_ok b6 vD vD1 aD aD1 (by rw [rd6, wr6]; exact rD) (by rw [rd6, wr6]; exact rD1)) (by decide))
    fun v7 ⟨⟨i7, T7, m7, b7⟩, k7⟩ => ?_)
  have rd7 : v7.rd = s.rd := k7.rd.trans rd6
  have wr7 : v7.wr = s.wr := k7.wr.trans wr6
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10, .r11, .lr]
    (fix3_ok (b7.trans b6) (d := BitVec.ofNat 32 d) (d1 := BitVec.ofNat 32 d1) (by rw [m7]; exact vD) (by rw [m7]; exact vD1) aD aD1 (by rw [rd7, wr7]; exact rD)
      (by rw [rd7, wr7]; exact rD1)) (by decide)) fun v8 ⟨⟨i8, T8, m8, b8⟩, k8⟩ => ?_)
  have b8' : v8.gpr .r12 = B := b8.trans (b7.trans b6)
  have wr8 : v8.wr = s.wr := k8.wr.trans wr7
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [] (Q := fun v =>
      v.mem = v8.mem.writeW (off (State.addr B) sQ) (v8.gpr .r1)) (by
    krun [b8', wr8, aQ, wQ]) (by decide)) fun v9 ⟨m9, k9⟩ => ?_)
  have hDv : (BitVec.ofNat 32 d).toNat * 2 ^ 32 + (BitVec.ofNat 32 d1).toNat = D := by rw [tn hd, tn hd1, hD]
  rw [hDv] at T7 T8
  generalize eT1 : (v6.gpr .r10).toNat + (v6.gpr .r11).toNat * 2 ^ 32 + (v6.gpr .lr).toNat * 2 ^ 64 = T1 at T6 T7
  generalize eT2 : (v7.gpr .r10).toNat + (v7.gpr .r11).toNat * 2 ^ 32 + (v7.gpr .lr).toNat * 2 ^ 64 = T2 at T7 T8
  have c1 : (2 ^ 31 ≤ (v6.gpr .lr).toNat) ↔ 2 ^ 95 ≤ T1 := by rw [← eT1]; exact top_bit_iff
  have c2 : (2 ^ 31 ≤ (v7.gpr .lr).toNat) ↔ 2 ^ 95 ≤ T2 := by rw [← eT2]; exact top_bit_iff
  have hUlt : U < 2 ^ 96 := by
    rw [hU]; have := (s.mem.readW (off (State.addr B) sU0) 32).isLt
    have := (s.mem.readW (off (State.addr B) sU2) 32).isLt; simp only [slot, w32]; omega
  have key := refine3_math (T1 := T1) (T2 := T2) hD0 (by omega) hUD hge hle hq0 hUlt hqD' T6
    (by rw [T7]; simp only [c1])
  refine k v9 ?_ ?_ (by rw [k9.gpr _ (by decide), b8']) ?_
  · simp only [slot]
    rw [m9, w32_write_self, i8, i7, i6, negOne_toNat, negOne_toNat, tn hq0]
    simp only [c1, c2]
    rw [← key]; omega
  · rw [m9, m8, m7, m6]; exact keep_write _ _ (by simp) (by simp only [sQ]; omega)
  · exact ((((k1.mono (by decide)).trans ((Preserves.toRest P2).mono (by decide))).trans
      ((k3.mono (by decide)).trans ((Preserves.toRest P4).mono (by decide)))).trans
      (((k5.mono (by decide)).trans (k6.mono (by decide))).trans
        ((k7.mono (by decide)).trans (k8.mono (by decide))))).trans (k9.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv
