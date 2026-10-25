module

import VerifiedGarbage.Proof.Bignum.PPC64LE.SqrSteps
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.SqrSteps
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontSqr
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Sqr

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.MontSqr
open VG.Proof.Bignum.PPC64LE

theorem sqr_shl (n k : Nat) (h : n * 2 ^ k < 2 ^ 64) : BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by
    have : n ≤ n * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _); omega)]

theorem prep_addr (B : Addr) {dB w i : Nat} (hi : i ≤ w) (hw' : w < 2 ^ 31) :
    BitVec.ofNat 64 (2 * w) <<< 2 + off B dB - BitVec.ofNat 64 (w - i) <<< 3 = off B (dB + 8 * i) := by
  rw [sqr_shl _ _ (by omega), sqr_shl _ _ (by omega),
    show 2 * w * 2 ^ 2 = (w - i) * 2 ^ 3 + 8 * i by omega, BitVec.ofNat_add, off, off, BitVec.ofNat_add]
  grind

/-- The registers `prep` writes. -/
def prepRegs : List Reg := [.r6, .r17, .r19, .r20, .r22]

/-- `prep`, for `aᵢ` at `da` (`r6`), `b` at `dB` (`r9`) and `r4 = w - i`:
`aᵢ` into `r17` and `b`'s word `i`, and `b`'s word `i + 1` less `aᵢ`'s top
bit. -/
theorem prep_ok {s : State} {B : Addr} {Z da dB w i : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h9 : s.gpr .r9 = off B dB) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s.gpr .r4 = BitVec.ofNat 64 (w - i)) (hi : i < w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hB : dB + 8 * i + 16 ≤ Z) :
    WP isa (.block prep) s fun s' =>
      (s'.gpr .r17 = word s.mem B da ∧ s'.gpr .r6 = off B (da + 8) ∧
        s'.mem = (s.mem.writeW (off B (dB + 8 * i)) (word s.mem B da)).writeW (off B (dB + 8 * i + 8))
          (word (s.mem.writeW (off B (dB + 8 * i)) (word s.mem B da)) B (dB + 8 * i + 8) -
            word s.mem B da >>> 63)) ∧ Keep prepRegs s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold prep
  prun [h6, h9, h11, h4, hs.ld ha, prep_addr B (dB := dB) (Nat.le_of_lt hi) hw',
    hs.st (show dB + 8 * i + 8 ≤ Z by omega), hs.ld (show dB + 8 * i + 8 + 8 ≤ Z by omega),
    hs.st (show dB + 8 * i + 8 + 8 ≤ Z by omega)]

/-- The registers `headR` writes. -/
def headRRegs : List Reg := [.r0, .r3, .r14, .r15, .r19, .r20, .r22]

/-- `headR`, `T` at `dA` (`r8`), `b` at `dB` (`r9`), `m` at `dM` (`r10`) and
`-m⁻¹ mod 2³²` in `r12`: `r0` a `u` with `2⁶⁴ d = t₀ + u m₀` for `d` in `r22`,
the pointers at word 0. -/
theorem headR_ok {s : State} {B : Addr} {Z dA dB dM : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dB) (h10 : s.gpr .r10 = off B dM)
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : dA + 8 ≤ Z) (hM : dM + 8 ≤ Z) :
    WP isa (.block headR) s fun s' =>
      (s'.gpr .r14 = off B dA ∧ s'.gpr .r15 = off B dB ∧ s'.gpr .r3 = off B dM ∧ s'.mem = s.mem ∧
        2 ^ 64 * (s'.gpr .r22).toNat = (word s.mem B dA).toNat + (s'.gpr .r0).toNat * (word s.mem B dM).toNat) ∧
      Keep headRRegs s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold headR
  mcrun [h8, h9, h10, hs.ld hA, hs.ld hM, BitVec.add_zero]
  have hm := mont_newton64 (word s.mem B dM) (s.gpr .r12) hinv
  have h2 := fios_red_arith (word s.mem B dA)
    (word s.mem B dA * ((word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12)) (word s.mem B dM) (by
    rw [BitVec.toNat_mul, BitVec.toNat_mul, Nat.mod_add_mod, Nat.add_comm]; exact mont_low _ _ _ hm)
  simp only [Nat.reducePow, word] at h2 ⊢
  omega

/-- The registers `head0` writes. -/
def head0Regs : List Reg := [.r0, .r3, .r14, .r15, .r18, .r19, .r20, .r22]

/-- `head0`: `fiosHead` with `aᵢ` in `r17` and `b` at `dB` (`r9`). -/
theorem head0_ok {s : State} {B : Addr} {Z dA dB dM : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dB) (h10 : s.gpr .r10 = off B dM)
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z) :
    WP isa (.block head0) s fun s' =>
      (s'.gpr .r14 = off B dA ∧ s'.gpr .r15 = off B dB ∧ s'.gpr .r3 = off B dM ∧ s'.mem = s.mem ∧
        2 ^ 64 * ((s'.gpr .r18).toNat + (s'.gpr .r22).toNat) = (word s.mem B dA).toNat +
          (s.gpr .r17).toNat * (word s.mem B dB).toNat + (s'.gpr .r0).toNat * (word s.mem B dM).toNat) ∧
      Keep head0Regs s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold head0
  mcrun [h8, h9, h10, hs.ld hA, hs.ld hB, hs.ld hM, BitVec.add_zero]
  have h1 := fios_head_arith (word s.mem B dA) (s.gpr .r17) (word s.mem B dB)
  have hm := mont_newton64 (word s.mem B dM) (s.gpr .r12) hinv
  have h2 := fios_red_arith (BitVec.ofNat 64 ((word s.mem B dA).toNat + (s.gpr .r17 * word s.mem B dB).toNat))
    (BitVec.ofNat 64 ((word s.mem B dA).toNat + (s.gpr .r17 * word s.mem B dB).toNat) *
      ((word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12)) (word s.mem B dM) (by
    rw [BitVec.toNat_mul, BitVec.toNat_mul, Nat.mod_add_mod, Nat.add_comm]; exact mont_low _ _ _ hm)
  simp only [Nat.reducePow, word] at h1 h2 ⊢
  omega

/-- The arithmetic of `top`: `c + t + d + p` as two words, the high word the
sum of the three carries. -/
theorem top_arith (c t d p : BitVec 64) :
    (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (c.toNat + t.toNat)).toNat + d.toNat)).toNat +
        p.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 ((0#64).toNat +
        (decide (2 ^ 64 ≤ c.toNat + t.toNat)).toNat)).toNat +
          (decide (2 ^ 64 ≤ (BitVec.ofNat 64 (c.toNat + t.toNat)).toNat + d.toNat)).toNat)).toNat +
        (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((BitVec.ofNat 64 (c.toNat + t.toNat)).toNat + d.toNat)).toNat +
          p.toNat)).toNat)).toNat =
      c.toNat + t.toNat + d.toNat + p.toNat := by
  have hc := c.isLt
  have ht := t.isLt
  have hd := d.isLt
  have hp := p.isLt
  simp only [BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + t.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ (c.toNat + t.toNat) % 2 ^ 64 + d.toNat <;>
    by_cases h3 : 2 ^ 64 ≤ ((c.toNat + t.toNat) % 2 ^ 64 + d.toNat) % 2 ^ 64 + p.toNat <;>
    simp only [h1, h2, h3, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A product by 0 or 1 is exact. -/
theorem mul_le_one (a b : BitVec 64) (h : b.toNat ≤ 1) : (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with e | e <;> rw [e]
  · simp
  · rw [Nat.mul_one]; exact Nat.mod_eq_of_lt a.isLt

theorem top_addr (B : Addr) (dB w : Nat) : BitVec.ofNat 64 (2 * w * 4) + off B dB = off B (dB + 8 * w) := by
  rw [off, off, BitVec.ofNat_add, show 2 * w * 4 = 8 * w by omega]
  grind

/-- `top`, `r14` at `dT`, `b` at `dB` (`r9`) and `n = 2 w` in `r11`, `b`'s
word `w` 0 or 1: the carries `c` (`r18`) and `d` (`r22`), the word at `dT +
8` and `aᵢ b_w` (`aᵢ` in `r17`), stored as two words at `dT`. -/
theorem top_ok {s : State} {B : Addr} {Z dT dB w : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B dT)
    (h9 : s.gpr .r9 = off B dB) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw' : w < 2 ^ 31)
    (hT : dT + 16 ≤ Z) (hB : dB + 8 * w + 8 ≤ Z) (hbw : (word s.mem B (dB + 8 * w)).toNat ≤ 1) :
    WP isa (.block top) s fun s' =>
      (∃ x y : BitVec 64, s'.mem = (s.mem.writeW (off B dT) x).writeW (off B (dT + 8)) y ∧
        x.toNat + 2 ^ 64 * y.toNat = (s.gpr .r18).toNat + (word s.mem B (dT + 8)).toNat + (s.gpr .r22).toNat +
          (s.gpr .r17).toNat * (word s.mem B (dB + 8 * w)).toNat) ∧
      Keep fiosRegs s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold top
  mcrun [h14, h9, h11, sqr_shl (2 * w) 2 (by omega), top_addr, hs.ld (show dB + 8 * w + 8 ≤ Z by omega), hs.ld (show dT + 8 + 8 ≤ Z by omega),
    hs.st (show dT + 8 ≤ Z by omega), hs.st (show dT + 8 + 8 ≤ Z by omega)]
  have h := top_arith (s.gpr .r18) (word s.mem B (dT + 8)) (s.gpr .r22) (s.gpr .r17 * word s.mem B (dB + 8 * w))
  have e := mul_le_one (s.gpr .r17) _ hbw
  simp only [Nat.reducePow, word] at h e ⊢
  refine ⟨_, _, rfl, ?_⟩
  rw [h, e]

theorem sqr_sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `rRem`: `(i - 1) mod 4` into `r16`, for `r4 = w - i`. -/
theorem rRem_ok {s : State} {w i : Nat} (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s.gpr .r4 = BitVec.ofNat 64 (w - i)) (hi : 1 ≤ i) (hiw : i ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.block rRem) s fun s' =>
      (s'.gpr .r16 = BitVec.ofNat 64 ((i - 1) % 4) ∧ s'.mem = s.mem) ∧ Keep [.r16] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rRem
  prun [h11, h4, mont_ofNat_shr1 (show w < 2 ^ 63 by omega), ofNat_sub_one (show 1 ≤ w by omega) (by omega),
    sqr_sub_ofNat (show w - i ≤ w - 1 by omega) (by omega), show w - 1 - (w - i) = i - 1 by omega,
    fios_rem (i - 1)]

/-- `rQuot`: `(i - 1) / 4` into `r16`, for `r4 = w - i`. -/
theorem rQuot_ok {s : State} {w i : Nat} (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s.gpr .r4 = BitVec.ofNat 64 (w - i)) (hi : 1 ≤ i) (hiw : i ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.block rQuot) s fun s' =>
      (s'.gpr .r16 = BitVec.ofNat 64 ((i - 1) / 4) ∧ s'.mem = s.mem) ∧ Keep [.r16] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rQuot
  prun [h11, h4, mont_ofNat_shr1 (show w < 2 ^ 63 by omega), ofNat_sub_one (show 1 ≤ w by omega) (by omega),
    sqr_sub_ofNat (show w - i ≤ w - 1 by omega) (by omega), show w - 1 - (w - i) = i - 1 by omega,
    fios_quot (i - 1) (by omega)]

/-- `li r18, 0` and `fRem`: `r18 := 0` and `r4 mod 4` into `r16`. -/
theorem fRem_ok {s : State} {n : Nat} (h4 : s.gpr .r4 = BitVec.ofNat 64 n) :
    WP isa (.block (.li .r18 0 :: fRem)) s fun s' =>
      (s'.gpr .r16 = BitVec.ofNat 64 (n % 4) ∧ s'.gpr .r18 = 0 ∧ s'.mem = s.mem) ∧ Keep [.r16, .r18] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold fRem
  prun [h4, fios_rem n]
  rfl

/-- `fQuot`: `r4 / 4` into `r16`. -/
theorem fQuot_ok {s : State} {n : Nat} (h4 : s.gpr .r4 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block fQuot) s fun s' =>
      (s'.gpr .r16 = BitVec.ofNat 64 (n / 4) ∧ s'.mem = s.mem) ∧ Keep [.r16] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold fQuot
  prun [h4, fios_quot n hn]

/-- The words `aᵢ bⱼ + u mⱼ` of a round and its top: the loops of
`fiosGroup`, counted from `r16` and then from what `Q` puts there, then
`top` and the rounds' count `r4` down by one. -/
def fpart (Q : List Instr) : Prog isa :=
  .seq (countLoop? (fiosGroup 1)) (.seq (.block Q) (.seq (countLoop? (fiosGroup unroll))
    (.block (top ++ [.subi .r4 .r4 1]))))

/-- The registers `fpart` writes. -/
def fpartRegs : List Reg := [.r3, .r4, .r14, .r15, .r16, .r18, .r19, .r20, .r22]

/-- The sum of `fpart`: that of the loops' `K` words, `W + P (c + d) = T + a S +
u M + C₀`, and of the top, `x + 2⁶⁴ y = c + t + d + a b`. -/
theorem fpart_sum {W T S M C₀ c d a u t b x y P : Nat}
    (e : W + P * (c + d) = T + a * S + u * M + C₀) (h : x + 2 ^ 64 * y = c + t + d + a * b) :
    W + P * (x + 2 ^ 64 * y) = T + P * t + a * (S + P * b) + u * M + C₀ := by
  rw [h]
  grind

/-- `fpart Q`, the pointers `r14`, `r15`, `r3` at `dT`, `dS`, `dM` and `K mod 4`
in `r16`, `Q` putting `K / 4` there; `b` at `dB` (`r9`), its word `w` (`dS +
8 K + 8`) 0 or 1: the `K + 2` words from `dT` are `T + aᵢ S + u M` plus the
carries, for `T` and `S` the `K + 1` words from `dT + 8` and `dS + 8` and `M`
the `K` words from `dM + 8`. -/
theorem fpart_ok {s : State} {B : Addr} {Z dT dS dM dB w K : Nat} {Q : List Instr} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B dT) (h15 : s.gpr .r15 = off B dS) (h3 : s.gpr .r3 = off B dM)
    (h16 : s.gpr .r16 = BitVec.ofNat 64 (K % 4)) (h9 : s.gpr .r9 = off B dB)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw' : w < 2 ^ 31) (hK : K < 2 ^ 31)
    (hQ : ∀ t : State, t.gpr .r4 = s.gpr .r4 → t.gpr .r11 = s.gpr .r11 →
      WP isa (.block Q) t fun t' => (t'.gpr .r16 = BitVec.ofNat 64 (K / 4) ∧ t'.mem = t.mem) ∧ Keep [.r16] t t')
    (hSw : dS + 8 * K + 8 = dB + 8 * w)
    (hT : dT + 8 * K + 16 ≤ Z) (hS : dS + 8 * K + 16 ≤ Z) (hM : dM + 8 * K + 8 ≤ Z)
    (sS : dS + 8 * K + 16 ≤ dT ∨ dT + 8 * K + 16 ≤ dS + 8)
    (sM : dM + 8 * K + 8 ≤ dT ∨ dT + 8 * K + 16 ≤ dM + 8)
    (hbw : (word s.mem B (dB + 8 * w)).toNat ≤ 1) :
    WP isa (fpart Q) s fun s' =>
      (Outside B dT (8 * (K + 2)) s.mem s'.mem ∧
        wordsVal s'.mem B dT (K + 2) = wordsVal s.mem B (dT + 8) (K + 1) +
          (s.gpr .r17).toNat * wordsVal s.mem B (dS + 8) (K + 1) + (s.gpr .r0).toNat * wordsVal s.mem B (dM + 8) K +
          ((s.gpr .r18).toNat + (s.gpr .r22).toNat) ∧
        s'.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1) ∧ Keep fpartRegs s s' := by
  have hnw := hs.nowrap
  have hK4 := Nat.mod_add_div K 4
  generalize hN₁ : K % 4 = N₁ at hK4 h16
  generalize hN₂ : K / 4 = N₂ at hK4 hQ
  have hN₁4 : N₁ < 4 := hN₁ ▸ Nat.mod_lt _ (by decide)
  unfold fpart
  -- Words `1` to `N₁`, one at a time.
  refine WP.seq (WP.mono (fiosLoop?_ok (U := 1) (N := N₁) (by decide) hs h14 h15 h3 h16 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₂ ⟨j14, j15, j3, jout, jeq, k₂⟩ => ?_)
  rw [Nat.one_mul] at j14 j15 j3 jout jeq
  -- The count of groups of four.
  refine WP.seq (WP.mono (hQ s₂ (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide))) fun s₃ ⟨⟨l16, lm⟩, k₃⟩ => ?_)
  have g₃ : ∀ r ∈ [Reg.r0, .r3, .r9, .r11, .r14, .r15, .r17, .r18, .r22], s₃.gpr r = s₂.gpr r := fun r hr =>
    k₃.gpr r (by revert r hr; decide)
  have g₂ : ∀ r ∈ [Reg.r0, .r9, .r11, .r17], s₂.gpr r = s.gpr r := fun r hr => k₂.gpr r (by revert r hr; decide)
  -- Words `N₁ + 1` to `K`, four at a time.
  refine WP.seq (WP.mono (fiosLoop?_ok (U := 4) (N := N₂) (dT := dT + 8 * N₁) (dB := dS + 8 * N₁)
    (dM := dM + 8 * N₁) (by decide) (hs.congr (k₂.trans k₃).wr) (by rw [g₃ .r14 (by decide), j14])
    (by rw [g₃ .r15 (by decide), j15]) (by rw [g₃ .r3 (by decide), j3]) l16 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun s₄ ⟨n14, _, _, nout, neq, k₄⟩ => ?_)
  have g₄ : ∀ r ∈ [Reg.r4, .r9, .r11, .r17], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (by revert r hr; decide), k₃.gpr r (by revert r hr; decide), k₂.gpr r (by revert r hr; decide)]
  -- The memory outside `T` is that on entry.
  have o₄ : Outside B dT (8 * K) s.mem s₄.mem :=
    (jout.mono (Nat.le_refl _) (by omega)).trans (by rw [← lm]; exact nout.mono (by omega) (by omega))
  -- Word `K + 1` and the carries.
  rw [WP.block_append_iff]
  refine WP.mono (top_ok (dT := dT + 8 * K) (dB := dB) (w := w) (hs.congr (k₂.trans (k₃.trans k₄)).wr)
    (by rw [n14, Nat.add_assoc, ← Nat.mul_add, show N₁ + 4 * N₂ = K by omega])
    (by rw [g₄ .r9 (by decide), h9]) (by rw [g₄ .r11 (by decide), h11]) hw' (by omega) (by omega)
    (by rw [o₄.word (by omega) (by omega)]; exact hbw))
    fun s₅ ⟨⟨x, y, tm, txy⟩, k₅⟩ => ?_
  refine WP.mono (subi_ok s₅ .r4 (by decide)) fun s₆ e6 => ?_
  subst e6
  have k25 := k₂.trans (k₃.trans (k₄.trans k₅))
  have pK : 2 ^ (64 * N₁) * 2 ^ (64 * (4 * N₂)) = 2 ^ (64 * K) := by
    rw [← Nat.pow_add, ← Nat.mul_add, hK4]
  refine ⟨⟨?_, ?_, by simp only [gpr_write, ↓reduceIte]; rw [k₅.gpr _ (by decide), g₄ .r4 (by decide)]⟩,
    ((k25.trans (Keep.write _ _ _)).mono (by decide))⟩
  · rw [mem_write, tm]
    exact (o₄.mono (Nat.le_refl _) (by omega)).trans
      (((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)).trans
        ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)))
  -- The words read by the second loop and the top are those on entry.
  have rd : ∀ d, (d + 8 * K + 8 ≤ dT ∨ dT + 8 * K + 16 ≤ d + 8 ∨ d = dT) → d + 8 * K + 8 ≤ Z →
      wordsVal s₃.mem B (d + 8 * N₁ + 8) (4 * N₂) = wordsVal s.mem B (d + 8 + 8 * N₁) (4 * N₂) := by
    intro d hd hdZ
    rw [lm, show d + 8 * N₁ + 8 = d + 8 + 8 * N₁ by omega, jout.wordsVal (by omega) (by omega)]
  have tw : word s₄.mem B (dT + 8 * K + 8) = word s.mem B (dT + 8 + 8 * K) := by
    rw [o₄.word (by omega) (by omega), show dT + 8 * K + 8 = dT + 8 + 8 * K by omega]
  have bw : word s₄.mem B (dB + 8 * w) = word s.mem B (dS + 8 + 8 * K) := by
    rw [o₄.word (by omega) (by omega), show dS + 8 + 8 * K = dB + 8 * w by omega]
  rw [rd dT (.inr (.inr rfl)) (by omega), rd dS (by omega) (by omega), rd dM (by omega) hM, g₃ .r0 (by decide),
    g₃ .r17 (by decide), g₃ .r18 (by decide), g₃ .r22 (by decide), g₂ .r0 (by decide), g₂ .r17 (by decide)] at neq
  rw [tw, bw, k₄.gpr .r17 (by decide), g₃ .r17 (by decide), g₂ .r17 (by decide)] at txy
  have e := fios_sum_group jeq neq rfl
  rw [← fios_wordsVal_append, ← fios_wordsVal_append, ← fios_wordsVal_append, hK4, pK] at e
  rw [show wordsVal s₂.mem B dT N₁ = wordsVal s₄.mem B dT N₁ by
      rw [← lm]; exact (nout.wordsVal (by omega) (by omega)).symm,
    ← fios_wordsVal_append, hK4] at e
  rw [mem_write, tm, show dT + 8 * K + 8 = dT + 8 * K + 8 from rfl, fios_wordsVal_write2 _ _ _ _ _ _ (by omega),
    wordsVal_succ_top s.mem B (dT + 8) K, wordsVal_succ_top s.mem B (dS + 8) K]
  exact fpart_sum e txy

/-- The arithmetic of `prep`: if `x₀ + 2⁶⁴ (r₀ + 2⁶⁴ R) = 2 (a + 2⁶⁴ H)`, `r₀`
less `a`'s top bit `c` does not borrow, and leaves `2 H`. -/
theorem prep_arith {x₀ r₀ R a H : Nat} (hx : x₀ < 2 ^ 64) (hr : r₀ < 2 ^ 64) (ha : a < 2 ^ 64)
    (h : x₀ + 2 ^ 64 * (r₀ + 2 ^ 64 * R) = 2 * (a + 2 ^ 64 * H)) :
    a / 2 ^ 63 ≤ r₀ ∧ r₀ - a / 2 ^ 63 + 2 ^ 64 * R = 2 * H := by
  omega

/-- `prep`'s stores, on `b`'s words from `i` (`n + 1` of them, `n ≥ 1`) that
were `2 (a + 2⁶⁴ H)` for `aᵢ = a`: they are `a + 2⁶⁴ (2 H)`, those from `i + 1`
are `2 H`, and the top one is 0 or 1. -/
theorem prep_buf {m : Mem} {B : Addr} {d n : Nat} {a : BitVec 64} {H : Nat} (hn : 1 ≤ n)
    (hd : d + 8 * (n + 1) ≤ 2 ^ 64) (hH : H < 2 ^ (64 * (n - 1)))
    (hbuf : wordsVal m B d (n + 1) = 2 * (a.toNat + 2 ^ 64 * H)) :
    let m₁ := m.writeW (off B d) a
    let m' := m₁.writeW (off B (d + 8)) (word m₁ B (d + 8) - a >>> 63)
    wordsVal m' B d (n + 1) = a.toNat + 2 ^ 64 * (2 * H) ∧ wordsVal m' B (d + 8) n = 2 * H ∧
      (word m' B (d + 8 + 8 * (n - 1))).toNat ≤ 1 ∧ Mont.Outside B d 16 m m' := by
  intro m₁ m'
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hH ⊢
  have o₁ : Mont.Outside B d 8 m m₁ := writeW_outside m B a (by omega)
  have o₂ : Mont.Outside B (d + 8) 8 m₁ m' := writeW_outside m₁ B _ (by omega)
  have w₁ : word m₁ B (d + 8) = word m B (d + 8) := o₁.word (by omega) (by omega)
  have rest : wordsVal m' B (d + 8 + 8) k = wordsVal m B (d + 8 + 8) k :=
    ((o₂.wordsVal (by omega) (by omega)).trans (o₁.wordsVal (by omega) (by omega)))
  have w0 : word m' B d = a := by
    rw [o₂.word (by omega) (by omega)]; exact word_writeW_self _ _ _ _
  have w8 : word m' B (d + 8) = word m B (d + 8) - a >>> 63 := by
    rw [word_writeW_self, w₁]
  rw [wordsVal, wordsVal] at hbuf
  have e := prep_arith (word m B d).isLt (word m B (d + 8)).isLt a.isLt hbuf
  have v8 : wordsVal m' B (d + 8) (k + 1) = 2 * H := by
    rw [wordsVal, rest, w8, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (word m B (d + 8)).isLt
    have : a.toNat / 2 ^ 63 < 2 ^ 64 := by have := a.isLt; omega
    rw [show 2 ^ 64 - a.toNat / 2 ^ 63 + (word m B (d + 8)).toNat =
      ((word m B (d + 8)).toNat - a.toNat / 2 ^ 63) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    exact e.2
  refine ⟨by rw [wordsVal, w0, v8], v8, ?_, (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))⟩
  -- The top word.
  have ht := wordsVal_succ_top m' B (d + 8) k
  rw [v8] at ht
  have hlt := wordsVal_lt m' B (d + 8) k
  have : 2 ^ (64 * k) * (word m' B (d + 8 + 8 * k)).toNat < 2 ^ (64 * k) * 2 := by omega
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)

/-- `fiosRem`: `(w - 1) mod 4` into `r16`. -/
theorem fiosRem_ok {s : State} {w : Nat} (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) :
    WP isa (.block fiosRem) s fun s' =>
      (s'.gpr .r16 = BitVec.ofNat 64 ((w - 1) % 4) ∧ s'.mem = s.mem) ∧ Keep [.r16] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold fiosRem
  prun [h11, mont_ofNat_shr1 (show w < 2 ^ 63 by omega), ofNat_sub_one hw (by omega), fios_rem (w - 1)]

/-- The registers a round writes: `tail`'s. -/
def sqRoundRegs : List Reg := [.r0, .r3, .r4, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

theorem round0_sum {C t0 a b0 u m0 F T1 S1 M1 : Nat} (h0 : 2 ^ 64 * C = t0 + a * b0 + u * m0)
    (hF : F = T1 + a * S1 + u * M1 + C) :
    2 ^ 64 * F = (t0 + 2 ^ 64 * T1) + a * (b0 + 2 ^ 64 * S1) + u * (m0 + 2 ^ 64 * M1) := by
  rw [hF]
  grind

/-- Round 0 (`round0`), for `a` at `da` (`r6`, advanced), `T` (`w + 1` words) at
`dA`, `b` (`w + 1` words) at `dB` holding `2 a`, `m` at `dM` and `r4 = w`: `b`'s
words from 1 are `2 (a ≫ 64)`, and `2⁶⁴ T' = T + a₀ (a₀ + 2⁶⁴ · 2 (a ≫ 64)) + u m`
for some `u < 2⁶⁴`. -/
theorem round0_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dB)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s.gpr .r4 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * (w + 1) ≤ Z) (hM : dM + 8 * w ≤ Z)
    (sAB : dA + 8 * (w + 1) ≤ dB ∨ dB + 8 * (w + 1) ≤ dA)
    (sAM : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM)
    (sBM : dM + 8 * w ≤ dB ∨ dB + 8 * (w + 1) ≤ dM)
    (hbuf : wordsVal s.mem B dB (w + 1) = 2 * wordsVal s.mem B da w) :
    WP isa round0 s fun s' =>
      (s'.gpr .r6 = off B (da + 8) ∧ s'.gpr .r4 = BitVec.ofNat 64 (w - 1) ∧
        Outs B [(dA, 8 * (w + 1)), (dB, 8 * (w + 1))] s.mem s'.mem ∧
        wordsVal s'.mem B (dB + 8) w = 2 * wordsVal s.mem B (da + 8) (w - 1) ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal s'.mem B dA (w + 1) = wordsVal s.mem B dA (w + 1) +
          (word s.mem B da).toNat * ((word s.mem B da).toNat + 2 ^ 64 * (2 * wordsVal s.mem B (da + 8) (w - 1))) +
          u * wordsVal s.mem B dM w) ∧
      Keep sqRoundRegs s s' := by
  have hnw := hs.nowrap
  unfold round0
  have hH := wordsVal_lt s.mem B (da + 8) (w - 1)
  have hbuf' : wordsVal s.mem B (dB + 8 * 0) ((w - 0) + 1) =
      2 * ((word s.mem B da).toNat + 2 ^ 64 * wordsVal s.mem B (da + 8) (w - 1)) := by
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, hbuf, fios_wordsVal_pred s.mem B da (by omega)]
  obtain ⟨b1, b2, b3, bo⟩ := prep_buf (m := s.mem) (B := B) (d := dB + 8 * 0) (n := w - 0) (by omega) (by omega)
    (by rw [Nat.sub_zero]; exact hH) hbuf'
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at b1 b2 b3 bo
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  -- `prep`.
  refine WP.mono (prep_ok (i := 0) hs h6 h9 h11 (by rw [h4, Nat.sub_zero]) (by omega) hw' (by omega) (by omega))
    fun s₁ ⟨⟨p17, p6, pm⟩, k₁⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at pm
  rw [← pm] at b1 b2 b3 bo
  have g₁ : ∀ r ∈ [Reg.r4, .r8, .r9, .r10, .r11, .r12], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr r (by revert r hr; decide)
  have wM : word s₁.mem B dM = word s.mem B dM := bo.word (by omega) (by omega)
  have wA : word s₁.mem B dA = word s.mem B dA := bo.word (by omega) (by omega)
  have vA : wordsVal s₁.mem B (dA + 8) w = wordsVal s.mem B (dA + 8) w := bo.wordsVal (by omega) (by omega)
  have vM : wordsVal s₁.mem B (dM + 8) (w - 1) = wordsVal s.mem B (dM + 8) (w - 1) :=
    bo.wordsVal (by omega) (by omega)
  have w0 : word s₁.mem B dB = word s.mem B da := by
    apply BitVec.eq_of_toNat_eq
    have := b1; rw [wordsVal, b2] at this; omega
  rw [WP.block_append_iff]
  -- Word 0.
  refine WP.mono (head0_ok (dA := dA) (dB := dB) (dM := dM) (hs.congr k₁.wr) (by rw [g₁ .r8 (by decide), h8])
    (by rw [g₁ .r9 (by decide), h9]) (by rw [g₁ .r10 (by decide), h10])
    (by rw [wM, g₁ .r12 (by decide)]; exact hinv) (by omega) (by omega) (by omega))
    fun s₂ ⟨⟨q14, q15, q3, qm, q0⟩, k₂⟩ => ?_
  have g₂ : ∀ r ∈ [Reg.r4, .r6, .r9, .r11, .r17], s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂.gpr r (by revert r hr; decide)
  -- `(w - 1) mod 4`.
  refine WP.mono (fiosRem_ok (w := w) (by rw [g₂ .r11 (by decide), g₁ .r11 (by decide), h11]) (by omega) hw')
    fun s₃ ⟨⟨r16, rm⟩, k₃⟩ => ?_
  have k13 := (k₁.trans (k₂.trans k₃))
  have g₃ : ∀ r ∈ [Reg.r0, .r3, .r4, .r6, .r9, .r11, .r14, .r15, .r17, .r18, .r22], s₃.gpr r = s₂.gpr r :=
    fun r hr => k₃.gpr r (by revert r hr; decide)
  have m31 : s₃.mem = s₁.mem := rm.trans qm
  -- Words `1` to `w`.
  refine WP.mono (fpart_ok (dT := dA) (dS := dB) (dM := dM) (dB := dB) (w := w) (K := w - 1) (Q := fiosQuot)
    (hs.congr k13.wr) (by rw [g₃ .r14 (by decide), q14]) (by rw [g₃ .r15 (by decide), q15])
    (by rw [g₃ .r3 (by decide), q3]) r16 (by rw [g₃ .r9 (by decide), g₂ .r9 (by decide), g₁ .r9 (by decide), h9])
    (by rw [g₃ .r11 (by decide), g₂ .r11 (by decide), g₁ .r11 (by decide), h11]) hw' (by omega)
    (fun t _ t11 => fiosQuot_ok (by rw [t11, g₃ .r11 (by decide), g₂ .r11 (by decide), g₁ .r11 (by decide), h11])
      (by omega) hw' |>.mono fun t' ⟨⟨a, b⟩, c⟩ => ⟨⟨a, b⟩, c⟩)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [m31, show dB + 8 * w = dB + 8 + 8 * (w - 1) by omega]; exact b3))
    fun s₄ ⟨⟨fo, fv, f4⟩, k₄⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, (s₂.gpr .r0).toNat, (s₂.gpr .r0).isLt, ?_⟩, ?_⟩
  · rw [k₄.gpr .r6 (by decide), g₃ .r6 (by decide), g₂ .r6 (by decide), p6]
  · rw [f4, g₃ .r4 (by decide), g₂ .r4 (by decide), g₁ .r4 (by decide), h4, ofNat_sub_one (by omega) (by omega)]
  · rw [m31] at fo
    exact Outs.trans (Outs.of_outside (o := dB) (n := 8 * (w + 1)) (bo.mono (Nat.le_refl _) (by omega)) (by simp))
      (Outs.of_outside (o := dA) (n := 8 * (w + 1)) (fo.mono (Nat.le_refl _) (by omega)) (by simp))
  · rw [← b2, ← m31]; exact fo.wordsVal (by omega) (by omega)
  · rw [g₃ .r17 (by decide), g₃ .r0 (by decide), g₃ .r18 (by decide), g₃ .r22 (by decide), g₂ .r17 (by decide), p17,
      m31, show w - 1 + 1 = w by omega, show w - 1 + 2 = w + 1 by omega, vA, vM, b2] at fv
    rw [wA, wM, w0, p17] at q0
    rw [fv, fios_wordsVal_pred s.mem B dA (show 1 ≤ w + 1 by omega), fios_wordsVal_pred s.mem B dM (show 1 ≤ w by omega),
      Nat.add_sub_cancel]
    exact round0_sum q0 rfl
  · exact (k13.trans k₄).mono

theorem roundI_sum {d0 t0 u m0 W1 P d2 T1 M1 F T2 a S M2 : Nat} (h0 : 2 ^ 64 * d0 = t0 + u * m0)
    (h1 : W1 + P * d2 = T1 + u * M1 + d0) (h2 : F = T2 + a * S + u * M2 + (0 + d2)) :
    2 ^ 64 * (W1 + P * F) = (t0 + 2 ^ 64 * (T1 + P * T2)) + 2 ^ 64 * P * (a * S) +
      u * (m0 + 2 ^ 64 * (M1 + P * M2)) := by
  rw [h2]
  grind

/-- Round `i` (`roundI`, `1 ≤ i < w`), as `round0_ok`: for `a` at `da` (`r6` at
`aᵢ`, advanced), `b`'s words from `i` holding `2 (a ≫ 64 i)` and `r4 = w - i`:
`b`'s words from `i + 1` hold `2 (a ≫ 64 (i + 1))`, and
`2⁶⁴ T' = T + 2^(64 i) aᵢ (aᵢ + 2⁶⁴ · 2 (a ≫ 64 (i + 1))) + u m` for some `u < 2⁶⁴`. -/
theorem roundI_ok {s : State} {B : Addr} {Z da dA dB dM w i : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B (da + 8 * i)) (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dB)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s.gpr .r4 = BitVec.ofNat 64 (w - i))
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hi : 1 ≤ i) (hiw : i < w) (hw' : w < 2 ^ 31)
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * (w + 1) ≤ Z) (hM : dM + 8 * w ≤ Z)
    (sAB : dA + 8 * (w + 1) ≤ dB ∨ dB + 8 * (w + 1) ≤ dA)
    (sAM : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM)
    (sBM : dM + 8 * w ≤ dB ∨ dB + 8 * (w + 1) ≤ dM)
    (hbuf : wordsVal s.mem B (dB + 8 * i) (w - i + 1) = 2 * wordsVal s.mem B (da + 8 * i) (w - i)) :
    WP isa roundI s fun s' =>
      (s'.gpr .r6 = off B (da + 8 * i + 8) ∧ s'.gpr .r4 = BitVec.ofNat 64 (w - i - 1) ∧
        Outs B [(dA, 8 * (w + 1)), (dB, 8 * (w + 1))] s.mem s'.mem ∧
        wordsVal s'.mem B (dB + 8 * i + 8) (w - i) = 2 * wordsVal s.mem B (da + 8 * i + 8) (w - i - 1) ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal s'.mem B dA (w + 1) = wordsVal s.mem B dA (w + 1) +
          2 ^ (64 * i) * ((word s.mem B (da + 8 * i)).toNat *
            ((word s.mem B (da + 8 * i)).toNat + 2 ^ 64 * (2 * wordsVal s.mem B (da + 8 * i + 8) (w - i - 1)))) +
          u * wordsVal s.mem B dM w) ∧
      Keep sqRoundRegs s s' := by
  have hnw := hs.nowrap
  have hH := wordsVal_lt s.mem B (da + 8 * i + 8) (w - i - 1)
  have hbuf' : wordsVal s.mem B (dB + 8 * i) ((w - i) + 1) =
      2 * ((word s.mem B (da + 8 * i)).toNat + 2 ^ 64 * wordsVal s.mem B (da + 8 * i + 8) (w - i - 1)) := by
    rw [hbuf, fios_wordsVal_pred s.mem B (da + 8 * i) (by omega)]
  obtain ⟨b1, b2, b3, bo⟩ := prep_buf (m := s.mem) (B := B) (d := dB + 8 * i) (n := w - i) (by omega) (by omega)
    hH hbuf'
  have hK4 := Nat.mod_add_div (i - 1) 4
  generalize hN₁ : (i - 1) % 4 = N₁ at hK4
  generalize hN₂ : (i - 1) / 4 = N₂ at hK4
  have hN₁4 : N₁ < 4 := hN₁ ▸ Nat.mod_lt _ (by decide)
  unfold roundI
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  -- `prep`.
  refine WP.mono (prep_ok (da := da + 8 * i) (i := i) hs h6 h9 h11 h4 hiw hw' (by omega) (by omega))
    fun s₁ ⟨⟨p17, p6, pm⟩, k₁⟩ => ?_
  rw [← pm] at b1 b2 b3 bo
  have g₁ : ∀ r ∈ [Reg.r4, .r8, .r9, .r10, .r11, .r12], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr r (by revert r hr; decide)
  have wM : word s₁.mem B dM = word s.mem B dM := bo.word (by omega) (by omega)
  -- Word 0.
  refine WP.mono (headR_ok (dA := dA) (dB := dB) (dM := dM) (hs.congr k₁.wr) (by rw [g₁ .r8 (by decide), h8])
    (by rw [g₁ .r9 (by decide), h9]) (by rw [g₁ .r10 (by decide), h10])
    (by rw [wM, g₁ .r12 (by decide)]; exact hinv) (by omega) (by omega))
    fun s₂ ⟨⟨q14, q15, q3, qm, q0⟩, k₂⟩ => ?_
  have g₂ : ∀ r ∈ [Reg.r4, .r6, .r9, .r11, .r17], s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂.gpr r (by revert r hr; decide)
  -- `(i - 1) mod 4`.
  refine WP.mono (rRem_ok (w := w) (i := i) (by rw [g₂ .r11 (by decide), g₁ .r11 (by decide), h11])
    (by rw [g₂ .r4 (by decide), g₁ .r4 (by decide), h4]) hi (by omega) hw') fun s₃ ⟨⟨r16, rm⟩, k₃⟩ => ?_
  rw [hN₁] at r16
  have k13 := k₁.trans (k₂.trans k₃)
  have g₃ : ∀ r ∈ [Reg.r0, .r3, .r4, .r6, .r9, .r11, .r14, .r15, .r17, .r22], s₃.gpr r = s₂.gpr r :=
    fun r hr => k₃.gpr r (by revert r hr; decide)
  have m31 : s₃.mem = s₁.mem := rm.trans qm
  -- Words `1` to `N₁`, `u mⱼ` alone.
  refine WP.seq (WP.mono (rLoop?_ok (U := 1) (N := N₁) (dT := dA) (dB := dB) (dM := dM) (by decide)
    (hs.congr k13.wr) (by rw [g₃ .r14 (by decide), q14]) (by rw [g₃ .r15 (by decide), q15])
    (by rw [g₃ .r3 (by decide), q3]) r16 (by omega) (by omega) (by omega) (by omega))
    fun s₄ ⟨j14, j15, j3, jout, jeq, k₄⟩ => ?_)
  rw [Nat.one_mul] at j14 j15 j3 jout jeq
  have g₄ : ∀ r ∈ [Reg.r0, .r4, .r6, .r9, .r11, .r17], s₄.gpr r = s₃.gpr r := fun r hr =>
    k₄.gpr r (by revert r hr; decide)
  -- `(i - 1) / 4`.
  refine WP.seq (WP.mono (rQuot_ok (w := w) (i := i)
    (by rw [g₄ .r11 (by decide), g₃ .r11 (by decide), g₂ .r11 (by decide), g₁ .r11 (by decide), h11])
    (by rw [g₄ .r4 (by decide), g₃ .r4 (by decide), g₂ .r4 (by decide), g₁ .r4 (by decide), h4]) hi (by omega) hw')
    fun s₅ ⟨⟨l16, lm⟩, k₅⟩ => ?_)
  rw [hN₂] at l16
  have g₅ : ∀ r ∈ [Reg.r0, .r3, .r4, .r6, .r9, .r11, .r14, .r15, .r17, .r22], s₅.gpr r = s₄.gpr r :=
    fun r hr => k₅.gpr r (by revert r hr; decide)
  -- Words `N₁ + 1` to `i - 1`, four at a time.
  refine WP.seq (WP.mono (rLoop?_ok (U := 4) (N := N₂) (dT := dA + 8 * N₁) (dB := dB + 8 * N₁)
    (dM := dM + 8 * N₁) (by decide) (hs.congr (k13.trans (k₄.trans k₅)).wr) (by rw [g₅ .r14 (by decide), j14])
    (by rw [g₅ .r15 (by decide), j15]) (by rw [g₅ .r3 (by decide), j3]) l16 (by omega) (by omega) (by omega)
    (by omega)) fun s₆ ⟨n14, n15, n3, nout, neq, k₆⟩ => ?_)
  have k36 := k₄.trans (k₅.trans k₆)
  have g₆ : ∀ r ∈ [Reg.r0, .r4, .r6, .r9, .r11, .r17], s₆.gpr r = s₃.gpr r := fun r hr => by
    rw [k₆.gpr r (by revert r hr; decide), g₅ r (by revert r hr; decide), g₄ r (by revert r hr; decide)]
  have r4₆ : s₆.gpr .r4 = BitVec.ofNat 64 (w - i) := by
    rw [g₆ .r4 (by decide), g₃ .r4 (by decide), g₂ .r4 (by decide), g₁ .r4 (by decide), h4]
  have pI : N₁ + 4 * N₂ = i - 1 := hK4
  -- The memory outside `T`'s words below `i - 1` is that after `prep`.
  have o₆ : Mont.Outside B dA (8 * (i - 1)) s₁.mem s₆.mem := by
    rw [← m31]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans (by rw [← lm]; exact nout.mono (by omega) (by omega))
  -- `r18 := 0` and `(w - i) mod 4`.
  refine WP.seq (WP.mono (fRem_ok r4₆) fun s₇ ⟨⟨f16, f18, fm⟩, k₇⟩ => ?_)
  have g₇ : ∀ r ∈ [Reg.r0, .r3, .r4, .r6, .r9, .r11, .r14, .r15, .r17, .r22], s₇.gpr r = s₆.gpr r :=
    fun r hr => k₇.gpr r (by revert r hr; decide)
  -- Words `i` to `w`.
  refine WP.mono (fpart_ok (dT := dA + 8 * (i - 1)) (dS := dB + 8 * (i - 1)) (dM := dM + 8 * (i - 1)) (dB := dB)
    (w := w) (K := w - i) (Q := fQuot) (hs.congr (k13.trans (k36.trans k₇)).wr)
    (by rw [g₇ .r14 (by decide), n14, Nat.add_assoc, ← Nat.mul_add, pI])
    (by rw [g₇ .r15 (by decide), n15, Nat.add_assoc, ← Nat.mul_add, pI])
    (by rw [g₇ .r3 (by decide), n3, Nat.add_assoc, ← Nat.mul_add, pI]) f16
    (by rw [g₇ .r9 (by decide), g₆ .r9 (by decide), g₃ .r9 (by decide), g₂ .r9 (by decide), g₁ .r9 (by decide), h9])
    (by rw [g₇ .r11 (by decide), g₆ .r11 (by decide), g₃ .r11 (by decide), g₂ .r11 (by decide),
      g₁ .r11 (by decide), h11]) hw' (by omega)
    (fun t t4 _ => fQuot_ok (by rw [t4, g₇ .r4 (by decide), r4₆]) (by omega) |>.mono fun t' ⟨⟨a, b⟩, c⟩ => ⟨⟨a, b⟩, c⟩)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [fm, o₆.word (d := dB + 8 * w) (by omega) (by omega), show dB + 8 * w = dB + 8 * i + 8 + 8 * (w - i - 1) by omega]
        exact b3))
    fun s₈ ⟨⟨fo, fv, f4⟩, k₈⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, (s₂.gpr .r0).toNat, (s₂.gpr .r0).isLt, ?_⟩, ?_⟩
  · rw [k₈.gpr .r6 (by decide), g₇ .r6 (by decide), g₆ .r6 (by decide), g₃ .r6 (by decide), g₂ .r6 (by decide), p6]
  · rw [f4, g₇ .r4 (by decide), r4₆, ofNat_sub_one (by omega) (by omega)]
  · rw [fm] at fo
    exact Outs.trans (Outs.of_outside (o := dB) (n := 8 * (w + 1)) (bo.mono (by omega) (by omega)) (by simp))
      (Outs.trans (Outs.of_outside (o := dA) (n := 8 * (w + 1)) (o₆.mono (Nat.le_refl _) (by omega)) (by simp))
        (Outs.of_outside (o := dA) (n := 8 * (w + 1)) (fo.mono (by omega) (by omega)) (by simp)))
  · rw [fm] at fo
    rw [← b2, fo.wordsVal (by omega) (by omega), o₆.wordsVal (by omega) (by omega)]
  · rw [fm] at fo fv
    -- Registers.
    have r0₇ : s₇.gpr .r0 = s₂.gpr .r0 := by rw [g₇ .r0 (by decide), g₆ .r0 (by decide), g₃ .r0 (by decide)]
    have r17₇ : s₇.gpr .r17 = word s.mem B (da + 8 * i) := by
      rw [g₇ .r17 (by decide), g₆ .r17 (by decide), g₃ .r17 (by decide), g₂ .r17 (by decide), p17]
    rw [r0₇, r17₇, f18, g₇ .r22 (by decide)] at fv
    rw [g₅ .r0 (by decide), g₄ .r0 (by decide), g₃ .r0 (by decide), g₅ .r22 (by decide)] at neq
    rw [g₃ .r0 (by decide), g₃ .r22 (by decide)] at jeq
    -- What the words were.
    have tS : ∀ d n, (d + 8 * n ≤ dB + 8 * i ∨ dB + 8 * i + 16 ≤ d) → d + 8 * n ≤ Z →
        wordsVal s₁.mem B d n = wordsVal s.mem B d n := fun d n h1 h2 => bo.wordsVal (by omega) (by omega)
    rw [m31, tS _ _ (by omega) (by omega), tS _ _ (by omega) (by omega)] at jeq
    rw [lm, show dA + 8 * N₁ + 8 = dA + 8 + 8 * N₁ by omega, show dM + 8 * N₁ + 8 = dM + 8 + 8 * N₁ by omega,
      jout.wordsVal (by omega) (by omega), jout.wordsVal (by omega) (by omega), m31,
      tS _ _ (by omega) (by omega), tS _ _ (by omega) (by omega)] at neq
    rw [show dA + 8 * (i - 1) + 8 = dA + 8 * i by omega, show dB + 8 * (i - 1) + 8 = dB + 8 * i by omega,
      show dM + 8 * (i - 1) + 8 = dM + 8 * i by omega, o₆.wordsVal (by omega) (by omega),
      o₆.wordsVal (by omega) (by omega), o₆.wordsVal (by omega) (by omega), b1,
      tS _ _ (by omega) (by omega), tS _ _ (by omega) (by omega)] at fv
    rw [wM, bo.word (d := dA) (by omega) (by omega)] at q0
    -- The words below `i - 1`.
    have e := r_sum_group jeq neq rfl
    rw [← fios_wordsVal_append, ← fios_wordsVal_append, pI,
      show 2 ^ (64 * N₁) * 2 ^ (64 * (4 * N₂)) = 2 ^ (64 * (i - 1)) by rw [← Nat.pow_add, ← Nat.mul_add, pI]] at e
    rw [show wordsVal s₄.mem B dA N₁ = wordsVal s₆.mem B dA N₁ by
        rw [← lm]; exact (nout.wordsVal (by omega) (by omega)).symm,
      ← fios_wordsVal_append, pI] at e
    have W1 : wordsVal s₈.mem B dA (i - 1) = wordsVal s₆.mem B dA (i - 1) := fo.wordsVal (by omega) (by omega)
    rw [← W1] at e
    -- Assemble.
    have hT8 := fios_wordsVal_append s₈.mem B dA (i - 1) (w - i + 2)
    rw [show i - 1 + (w - i + 2) = w + 1 by omega] at hT8
    have hT := fios_wordsVal_append s.mem B (dA + 8) (i - 1) (w - i + 1)
    rw [show i - 1 + (w - i + 1) = w by omega, show dA + 8 + 8 * (i - 1) = dA + 8 * i by omega] at hT
    have hMv := fios_wordsVal_append s.mem B (dM + 8) (i - 1) (w - i)
    rw [show i - 1 + (w - i) = w - 1 by omega, show dM + 8 + 8 * (i - 1) = dM + 8 * i by omega] at hMv
    have hP : 2 ^ (64 * i) = 2 ^ 64 * 2 ^ (64 * (i - 1)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hT8, fios_wordsVal_pred s.mem B dA (show 1 ≤ w + 1 by omega), Nat.add_sub_cancel, hT,
      fios_wordsVal_pred s.mem B dM (show 1 ≤ w by omega), hMv, hP]
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at fv
    have := roundI_sum q0 e fv
    rw [this]
  · exact (k13.trans (k36.trans (k₇.trans k₈))).mono

end VG.Proof.Bignum.PPC64LE.Sqr
