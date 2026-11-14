module

public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Proof.X448.BaseTable
import Mathlib.Algebra.Module.NatInt
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.X448.Ladder
public import VerifiedGarbage.Proof.X448.AArch64.Swap
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Curve448.AArch64.Swap

/-! ### `X448.BaseDigits`, which only this module used -/

section

/-!
# The fixed-base comb's digits and partial sums

As `Proof/Ed25519/CombDigits.lean` for Ed25519's comb, for `8n` bits (448 for
X448, 456 for Ed448). The scalar `S < 256^n` has `2n` nibbles `n_i`; the digits
are `d_i = n_i - 8`, from `-8` to `7`. Step `j < n` adds `d_{2j+1} 256^j` to one
accumulator and `d_{2j} 256^j` to another, both starting at `G = combG n`; 16
times the first plus the second is `S` (`comb_total`), since
`G = 8 Σ_{j < n} 256^j`.

A negative digit adds the negation `(-x, y)` of the table entry `|d|`
(`baseEntry_ok`).
-/

@[expose] public section

namespace VG.Proof.X448

open VG.Impl.X448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open Spec.X448 (Fe)

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 256 ^ c

theorem pow_256 (n : Nat) : 256 ^ n = 16 ^ (2 * n) := by
  rw [Nat.pow_mul]

theorem comb_partial (S : Nat) : ∀ n, 16 * oddSum S n + evenSum S n = S % 256 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have hd : S / 16 ^ (2 * n + 1) = S / 16 ^ (2 * n) / 16 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have hm : S % 256 ^ (n + 1) = S % 256 ^ n + 256 ^ n * (S / 256 ^ n % 256) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, pow_256]
    generalize S / 16 ^ (2 * n) = x
    generalize 16 ^ (2 * n) = y
    have : x % 256 = x % 16 + 16 * (x / 16 % 16) := by omega_arith
    rw [this]; ring

/-- `Σ_{j < c} 256^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 256 ^ c

/-- The constant the digits of a comb of `n` tables are offset by: `8 Σ_{j < n} 256^j`. -/
def combG (n : Nat) : Nat := 8 * geom n

theorem combG_56 : combG 56 = baseGVal := by decide

theorem combG_57 : combG 57 = baseGVal57 := by decide

/-- The comb's digit `i`: `n_i - 8`, from `-8` to `7`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 8

/-- `Σ_{j < c} d_{2j+1} 256^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} d_{2j} 256^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 256 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The two accumulators' multiples of `B` give the scalar: `16 (G + Σ_j d_{2j+1} 256^j) +
(G + Σ_j d_{2j} 256^j) = S`. -/
theorem comb_total {n S : Nat} (hS : S < 256 ^ n) :
    16 * ((combG n : ℤ) + oddSumZ S n) + (combG n + evenSumZ S n) = S := by
  simp only [oddSumZ_eq, evenSumZ_eq, combG]
  have h := comb_partial S n
  rw [Nat.mod_eq_of_lt hS] at h
  have h' : (16 * oddSum S n + evenSum S n : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

/-- A nibble from its four bits. -/
theorem nib_bits (S i : Nat) :
    nib S i = (((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2 := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [Nat.pow_mul]
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [nib, e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [Nat.pow_zero, Nat.div_one, Nat.reducePow]
  omega_arith

theorem nib_lt (S i : Nat) : nib S i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem mag_lt {n : Nat} (hn : n < 16) : mag n < 9 := by unfold mag; split <;> omega_arith

/-- The affine point `(x, y)` negated: `(-x, y)`. -/
def negAff (q : Fe × Fe) : Fe × Fe := (0 - q.1, q.2)

theorem basePt_neg (q : Fe × Fe) : basePt (negAff q) = negPoint (basePt q) := rfl

/-- The entry for the digit `n - 8` of table `j`, negated for a negative digit, represents
`[(n - 8) 256^j] B`. -/
theorem baseEntry_ok (j n : Nat) (hj : j < 57) (hn : n < 16) :
    Rep (basePt (if n < 8 then negAff (baseTable j (mag n)) else baseTable j (mag n)))
      ((((n : ℤ) - 8) * 256 ^ j) • baseAff) := by
  have hr := baseTable_ok j (mag n) hj (mag_lt hn)
  by_cases hlt : n < 8
  · simp only [hlt, ↓reduceIte, basePt_neg]
    have e : ((n : ℤ) - 8) * 256 ^ j = -(((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega_arith : n ≤ 8)]; ring
    rw [e, neg_smul, natCast_zsmul]
    exact hr.neg
  · simp only [hlt, ↓reduceIte]
    have e : ((n : ℤ) - 8) * 256 ^ j = (((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega_arith : 8 ≤ n)]; ring
    rw [e, natCast_zsmul]
    exact hr

end VG.Proof.X448

end

end


/-!
# X448 of the base point on AArch64: the comb's digits and masks

Untrusted: everything here is checked by Lean. As Ed25519's comb
(`Proof/Ed25519/AArch64/CombDigit.lean`): step `j` reads the nibbles `2j + 1`
and `2j` of the decoded scalar from its bits (one per byte at `BITS`) by
Horner's rule; `magnitude` turns each into `|n - 8|`; `masks` sets the register
for `m` to all ones exactly if the magnitude is `m`, for `m = 1 … 8`, and
another to `1` exactly if it is `0`.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off contains_sc read1_eq)
open VG.Proof.X448 (nib nib_bits nib_lt mag mag_lt)
open VG.Proof.Curve448.AArch64 (mask)

/-- The `8n` bits of the scalar `k` (for a comb of `n` tables), one per byte at `BITS`, as
`bits_ok` leaves them. -/
def Bits (n : Nat) (base : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 8 * n, m (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)

theorem bit_eq (k t : Nat) : VG.Proof.X448.bit k t = (k / 2 ^ t) % 2 := by
  simp only [VG.Proof.X448.bit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-! ## The bit index -/

private theorem index_fact : ∀ j < 57, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem index_ok (s : State) {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 57)
    (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.lsl .x .x8 .x19 3, .add .x .x8 .x3 .x8] : List Instr)) s fun t =>
      t.gpr .x8 = off base (8 * j) ∧ Keeps [.x8] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (3 : Nat) < 64 from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hb, index_fact j hj, hs.x3, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The nibble -/

private theorem bit_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

theorem nibble_ok {s : State} {base : Addr} (hs : Scr s base) {n k i p o : Nat} (hn : n ≤ 57)
    (hi : i < 2 * n) (hp : s.gpr .x8 = off base p) (hpo : p + o = BITS + 4 * i) (ho : o + 3 < 4096)
    (hb : Bits n base k s.mem) :
    WP isa (.block (nibble o)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib k i) ∧ Keeps [.x2, .x9] s t ∧ t.mem = s.mem := by
  have hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off base (BITS + (4 * i + j))) 1 := fun j hj =>
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [hn, hi, hj])⟩
  have he : ∀ j, off base p + BitVec.ofNat 64 (o + j) = off base (BITS + (4 * i + j)) :=
    fun j => by
      simp only [off]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (base + ·) (congrArg (BitVec.ofNat 64) (by omega_using [hpo]))
  have hv : ∀ j < 4, ((s.mem (off base (BITS + (4 * i + j)))).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 ((k / 2 ^ (4 * i + j)) % 2) := fun j hj => by
    rw [hb _ (by omega_using [hi, hj]), bit_eq]; exact bit_ext _ (Nat.mod_lt _ (by decide))
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  have e3 := he 3
  simp only [Nat.add_zero] at e0
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at v0 r0
  apply WP.of_runBlock
  simp only [nibble, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, Nat.mod_one,
    show o + 3 < 4096 * 1 by omega_using [ho], show o + 2 < 4096 * 1 by omega_using [ho], show o + 1 < 4096 * 1 by omega_using [ho],
    show o < 4096 * 1 by omega_using [ho],
    Nat.reduceMul, and_self, hp, e0, e1, e2, e3,
    r0, r1, r2, r3, read1_eq, v0, v1, v2, v3,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · rw [nib_bits]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## Sign and magnitude -/

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^
        (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63)) -
      (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) =
      BitVec.ofNat 64 (mag n) ∧
    ((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63 =
      mask (decide (n < 8)) := by
  decide +kernel

theorem magnitude_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x2 = BitVec.ofNat 64 n) :
    WP isa (.block magnitude) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x1 = mask (decide (n < 8)) ∧
      Keeps [.x1, .x2, .x9] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [magnitude, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (8 : Nat) < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    show 16 * 0 < 32 from by decide, Nat.mul_zero, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, (sign_fact n hn).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## The masks -/

/-- The bit of `|d| = 0`. -/
def zeroBit (a : Nat) : BitVec 64 := if a = 0 then 1 else 0

private theorem less_fact : ∀ a < 9, ∀ k < 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 1)) >>> 63 -
      (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 2)) >>> 63 = mask (decide (a = k + 1)) := by
  decide +kernel

private theorem last_fact : ∀ a < 9,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 8) >>> 63 - BitVec.ofNat 64 1 = mask (decide (a = 8)) ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 1) >>> 63 = zeroBit a := by
  decide +kernel

theorem masksOdd_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (masks oddRegs .x5)) s fun t =>
      (∀ m, 1 ≤ m → m ≤ 8 → t.gpr (oddReg m) = mask (decide (a = m))) ∧ t.gpr .x5 = zeroBit a ∧
      Keeps [.x5, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x4] s t ∧ t.mem = s.mem := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [masks, oddRegs, oddReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega_using [hk],
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun m hm1 hm8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega_using [hm1, hm8]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem masksEven_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (masks evenRegs .x0)) s fun t =>
      (∀ m, 1 ≤ m → m ≤ 8 → t.gpr (evenReg m) = mask (decide (a = m))) ∧ t.gpr .x0 = zeroBit a ∧
      Keeps [.x0, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t ∧ t.mem = s.mem := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [masks, evenRegs, evenReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega_using [hk],
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun m hm1 hm8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega_using [hm1, hm8]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## Both digits -/

/-- The registers `digits` writes. -/
def digitRegs : List Reg :=
  [.x8, .x2, .x9, .x1, .x5, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x4,
    .x0, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- What `digits` leaves for step `j`'s two digits of the scalar `k`. -/
structure DigitsOut (s : State) (k j : Nat) (t : State) : Prop where
  oddMask : ∀ m, 1 ≤ m → m ≤ 8 → t.gpr (oddReg m) = mask (decide (mag (nib k (2 * j + 1)) = m))
  oddZero : t.gpr .x5 = zeroBit (mag (nib k (2 * j + 1)))
  evenMask : ∀ m, 1 ≤ m → m ≤ 8 → t.gpr (evenReg m) = mask (decide (mag (nib k (2 * j)) = m))
  evenZero : t.gpr .x0 = zeroBit (mag (nib k (2 * j)))
  keeps : Keeps digitRegs s t

theorem digits_ok {s : State} {base : Addr} (hs : Scr s base) {n k j : Nat} (hn : n ≤ 57) (hj : j < n)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hb : Bits n base k s.mem) :
    WP isa (.block digits) s fun t => DigitsOut s k j t ∧ t.mem = s.mem := by
  have no : nib k (2 * j + 1) < 16 := nib_lt _ _
  have ne : nib k (2 * j) < 16 := nib_lt _ _
  simp only [digits, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (index_ok s hs (by omega_using [hn, hj]) hc) fun a ⟨a8, ka, ma⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nibble_ok hsa hn (k := k) (i := 2 * j + 1) (by omega_using [hj]) a8 (by simp only [BITS]; omega_using [])
    (by decide) (by rw [ma]; exact hb)) fun b ⟨b2, kb, mb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok b no b2) fun c ⟨c2, _, kc, mc⟩ => ?_
  have hsc := (hsa.of_keeps kb (by decide)).of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masksOdd_ok _ (mag_lt no) c2) fun e ⟨em, ez, ke, me⟩ => ?_
  have e8 : e.gpr .x8 = off base (8 * j) := by
    rw [ke.1 _ (by decide), kc.1 _ (by decide), kb.1 _ (by decide), a8]
  have hse : Scr e base := hsc.of_keeps ke (by decide)
  have hbe : Bits n base k e.mem := fun q hq => by
    rw [me, mc, mb, ma]; exact hb q hq
  rw [WP.block_append_iff]
  refine WP.mono (nibble_ok hse hn (k := k) (i := 2 * j) (by omega_using [hj]) e8 (by simp only [BITS]; omega_using [])
    (by decide) hbe) fun f ⟨f2, kf, mf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok f ne f2) fun g ⟨g2, _, kg, mg⟩ => ?_
  refine WP.mono (masksEven_ok _ (mag_lt ne) g2) fun t ⟨tm, tz, kt, mt⟩ => ?_
  refine ⟨⟨fun m h1 h8 => ?_, ?_, tm, tz, ?_⟩, by rw [mt, mg, mf, me, mc, mb, ma]⟩
  · have hk : ∀ m < 9, oddReg m ∉ [Reg.x0, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] ∧
        oddReg m ∉ [Reg.x1, .x2, .x9] ∧ oddReg m ∉ [Reg.x2, .x9] := by
      decide
    obtain ⟨ht, hg, hf⟩ := hk m (by omega_using [h8])
    rw [kt.1 _ ht, kg.1 _ hg, kf.1 _ hf]
    exact em m h1 h8
  · rw [kt.1 _ (by decide), kg.1 _ (by decide), kf.1 _ (by decide)]
    exact ez
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [digitRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kt.1 _ (by simp [hr]), kg.1 _ (by simp [hr]), kf.1 _ (by simp [hr]),
        ke.1 _ (by simp [hr]), kc.1 _ (by simp [hr]), kb.1 _ (by simp [hr]), ka.1 _ (by simp [hr])]
    · rw [kt.2.1, kg.2.1, kf.2.1, ke.2.1, kc.2.1, kb.2.1, ka.2.1]
    · rw [kt.2.2, kg.2.2, kf.2.2, ke.2.2, kc.2.2, kb.2.2, ka.2.2]

end VG.Proof.X448.AArch64.Base
