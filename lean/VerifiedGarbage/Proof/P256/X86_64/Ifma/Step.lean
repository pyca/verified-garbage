module

import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Arith
public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Code
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Sym

/-! ### `P256.X86_64.Ifma.Glue`, which this module and modules that import it used -/

section

/-! ### `P256.X86_64.Ifma.Stage`, which this module and modules that import it used -/

section

/-!
# P-256 on x86-64 with AVX512_IFMA: a stage of a block

The code of a block is in pieces, one for each stage (`Impl/…/Ifma/Code.lean`),
with the places (`Loc`) of the values between them. `tops` reads a stage as
terms (`T`): what `VSym.run` makes of the instructions `allocCuts` writes
for each operation, whatever registers it chose. `chkSeg`, which the kernel
evaluates, checks that the piece's code, run from the places the stage's
values are in, leaves in the places of its results the terms the stage
gives; `stage_wp` then says what the piece does: each quadword of each
place is its term, of the state before.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## Terms as integers

The limbs of the field arithmetic are signed: a difference is a `vpsubq`, a
carry a `vpsraq`. `T.int` is the value of a term as an integer, with no
reduction modulo `2⁶⁴`; a quadword the code computes is that integer modulo
`2⁶⁴` (`R64`) wherever each logical shift right is of a number in
`[0, 2⁶⁴)` and each arithmetic one of a number in `[-2⁶³, 2⁶³)`. `T.iv`
bounds each term from the bounds of the registers and memory a block starts
from, and is `none` where a shift's operand might be out of its range;
`iv_ok` proves that a term is `T.int` modulo `2⁶⁴` and within `T.iv` where
the kernel evaluates `T.iv` of concrete terms.
-/

section

open VG VG.X86_64
open VG.Proof.Bignum.X86_64.Ifma (qv)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4 sel4_lt)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-- The values a block starts from, as integers: quadword `k` of register
`r`, and of the 32 bytes at `b + d`. -/
structure Env where
  v : Nat → Nat → Int
  m : Reg → Nat → Nat → Int

/-- The registers through which the words of field elements are read, each a number below `2⁶⁴`:
the other quadwords are signed. -/
def uBase (b : Reg) : Bool := b == .rcx || b == .rdx

def envOf (s₀ : State) : Env :=
  ⟨fun r k => (qv s₀ (vreg r) k).toInt,
    fun b d k => if uBase b then ((s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).toNat : Int)
      else (s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).toInt⟩

/-- The value of a term as an integer, with no reductions modulo `2⁶⁴`. -/
def T.int (E : Env) : T → Nat → Int
  | .reg r, k => E.v r k
  | .lit a b c d, k => (pick4 a b c d k : Nat)
  | .ld b d, k => E.m b d k
  | .add a b, k => a.int E k + b.int E k
  | .sub a b, k => a.int E k - b.int E k
  | .shl a n, k => a.int E k * 2 ^ n
  | .shr a n, k => a.int E k / 2 ^ n
  | .sra a n, k => a.int E k / 2 ^ n
  | .mask a j0 j1 j2 j3, k => if 64 ≤ pick4 j0 j1 j2 j3 k then a.int E k else a.int E k % 2 ^ pick4 j0 j1 j2 j3 k
  | .blend a b m, k => if m.testBit k then b.int E k else a.int E k
  | .perm a o, k => a.int E (sel4 o k)
  | .mad false c a b, k => c.int E k + a.int E k % 2 ^ 52 * (b.int E k % 2 ^ 52) % 2 ^ 52
  | .mad true c a b, k => c.int E k + a.int E k % 2 ^ 52 * (b.int E k % 2 ^ 52) / 2 ^ 52
  | .slr a n j, k => a.int E k * 2 ^ n % 2 ^ 64 / 2 ^ j
  | .sel c a b, k => if c.int E k = 0 then a.int E k else b.int E k

/-- Bounds on what a block starts from, from below and above. -/
structure Bnds where
  vl : Nat → Nat → Int
  vh : Nat → Nat → Int
  ml : Reg → Nat → Nat → Int
  mh : Reg → Nat → Nat → Int

/-- The bound on the low 52 bits of a number in an interval. -/
def cap (x : Int × Int) : Int := if 0 ≤ x.1 ∧ x.2 < 2 ^ 52 then x.2 else 2 ^ 52 - 1

/-- Bounds on a term, from below and above, or `none` where a shift's
operand may be out of range. -/
def T.iv (B : Bnds) : T → Nat → Option (Int × Int)
  | .reg r, k => some (B.vl r k, B.vh r k)
  | .lit a b c d, k => some ((pick4 a b c d k : Nat), (pick4 a b c d k : Nat))
  | .ld b d, k => some (B.ml b d k, B.mh b d k)
  | .add a b, k => (a.iv B k).bind fun x => (b.iv B k).map fun y => (x.1 + y.1, x.2 + y.2)
  | .sub a b, k => (a.iv B k).bind fun x => (b.iv B k).map fun y => (x.1 - y.2, x.2 - y.1)
  | .shl a n, k => (a.iv B k).map fun x => (x.1 * 2 ^ n, x.2 * 2 ^ n)
  | .shr a n, k => (a.iv B k).bind fun x =>
    if 0 ≤ x.1 ∧ x.2 < 2 ^ 64 then some (x.1 / 2 ^ n, x.2 / 2 ^ n) else none
  | .sra a n, k => (a.iv B k).bind fun x =>
    if -2 ^ 63 ≤ x.1 ∧ x.2 < 2 ^ 63 then some (x.1 / 2 ^ n, x.2 / 2 ^ n) else none
  | .mask a j0 j1 j2 j3, k => (a.iv B k).bind fun x =>
    if 64 < pick4 j0 j1 j2 j3 k then none
    else if 64 ≤ pick4 j0 j1 j2 j3 k then some x
    else if 0 ≤ x.1 ∧ x.2 < 2 ^ pick4 j0 j1 j2 j3 k then some x
    else some (0, 2 ^ pick4 j0 j1 j2 j3 k - 1)
  | .blend a b m, k => if m.testBit k then b.iv B k else a.iv B k
  | .perm a o, k => a.iv B (sel4 o k)
  | .mad false c a b, k => (c.iv B k).bind fun x => (a.iv B k).bind fun _ => (b.iv B k).map fun _ =>
    (x.1, x.2 + (2 ^ 52 - 1))
  | .mad true c a b, k => (c.iv B k).bind fun x => (a.iv B k).bind fun y => (b.iv B k).map fun z =>
    (x.1, x.2 + cap y * cap z / 2 ^ 52)
  | .slr a _ j, k => (a.iv B k).map fun _ => (0, (2 ^ 64 - 1) / 2 ^ j)
  | .sel c a b, k => (c.iv B k).bind fun x => (a.iv B k).bind fun y => (b.iv B k).bind fun z =>
    if -1 ≤ x.1 ∧ x.2 ≤ 0 then some (min y.1 z.1, max y.2 z.2) else none

/-- What a block starts from is within `B`. -/
structure EnvOK (s₀ : State) (B : Bnds) : Prop where
  v : ∀ r k, k < 4 → B.vl r k ≤ (envOf s₀).v r k ∧ (envOf s₀).v r k ≤ B.vh r k
  m : ∀ b d k, k < 4 → B.ml b d k ≤ (envOf s₀).m b d k ∧ (envOf s₀).m b d k ≤ B.mh b d k

/-! ## Quadwords as integers modulo `2⁶⁴` -/

/-- The quadword `x` is the integer `X` modulo `2⁶⁴`. -/
def R64 (x : BitVec 64) (X : Int) : Prop := x.toNat = (X % 2 ^ 64).toNat

theorem R64.toInt (x : BitVec 64) : R64 x x.toInt := by
  have := x.isLt
  rw [R64, BitVec.toInt_eq_toNat_cond]
  split <;> omega_using []

theorem R64.toNat (x : BitVec 64) : R64 x (x.toNat : Int) := by
  have := x.isLt
  rw [R64]; omega_using []

theorem R64.ofNat (w : Nat) : R64 (BitVec.ofNat 64 w) (w : Int) := by
  rw [R64, BitVec.toNat_ofNat]; omega_using []

theorem R64.add {x y : BitVec 64} {X Y : Int} (hx : R64 x X) (hy : R64 y Y) : R64 (x + y) (X + Y) := by
  rw [R64] at *; rw [BitVec.toNat_add]; omega_using [hx, hy]

theorem R64.sub {x y : BitVec 64} {X Y : Int} (hx : R64 x X) (hy : R64 y Y) : R64 (x - y) (X - Y) := by
  have := y.isLt
  rw [R64] at *; rw [BitVec.toNat_sub]; omega_using [hx, hy]

/-- A number in `[0, 2⁶⁴)` is its quadword's. -/
theorem R64.nat {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : 0 ≤ X) (h1 : X < 2 ^ 64) : (x.toNat : Int) = X := by
  rw [R64] at hx; omega_using [hx, h0, h1]

/-- A number in `[-2⁶³, 2⁶³)` is its quadword's, signed. -/
theorem R64.int {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : -2 ^ 63 ≤ X) (h1 : X < 2 ^ 63) : x.toInt = X := by
  have := x.isLt
  rw [R64] at hx
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega_arith

theorem emod_mul_pow (X : Int) (q : Int) : (X % 2 ^ 64 * q) % 2 ^ 64 = (X * q) % 2 ^ 64 := by
  have e : X * q = X % 2 ^ 64 * q + 2 ^ 64 * (X / 2 ^ 64 * q) := by
    have : X = X % 2 ^ 64 + 2 ^ 64 * (X / 2 ^ 64) := by omega_using []
    grind
  rw [e, Int.add_mul_emod_self_left]

theorem R64.shl {x : BitVec 64} {X : Int} (hx : R64 x X) (n : Nat) : R64 (x <<< n) (X * 2 ^ n) := by
  rw [R64] at *
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx, ← emod_mul_pow]
  have h0 : 0 ≤ X % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
  rw [hN, Int.toNat_natCast, show ((N : Int) * 2 ^ n) = ((N * 2 ^ n : Nat) : Int) by push_cast; rfl]
  omega_using []

theorem R64.shr {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : 0 ≤ X) (h1 : X < 2 ^ 64) (n : Nat) :
    R64 (x >>> n) (X / 2 ^ n) := by
  have e := hx.nat h0 h1
  rw [R64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← e,
    show ((x.toNat : Int) / 2 ^ n) = ((x.toNat / 2 ^ n : Nat) : Int) by push_cast; rfl]
  have := Nat.div_le_self x.toNat (2 ^ n)
  have := x.isLt
  generalize x.toNat / 2 ^ n = K at *
  omega_using [this]

theorem R64.sra {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : -2 ^ 63 ≤ X) (h1 : X < 2 ^ 63) (n : Nat) :
    R64 (x.sshiftRight n) (X / 2 ^ n) := by
  have e := hx.int h0 h1
  have r := R64.toInt (x.sshiftRight n)
  rw [BitVec.toInt_sshiftRight, e, Int.shiftRight_eq_div_pow] at r
  exact r

theorem R64.mask {x : BitVec 64} {X : Int} (hx : R64 x X) {j : Nat} (hj : j ≤ 64) :
    R64 (x &&& BitVec.ofNat 64 (2 ^ j - 1)) (if 64 ≤ j then X else X % 2 ^ j) := by
  have hp : 2 ^ j ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hj
  have hp0 : 0 < 2 ^ j := Nat.pos_of_ne_zero (by simp)
  have e : (x &&& BitVec.ofNat 64 (2 ^ j - 1)).toNat = x.toNat % 2 ^ j := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hp]), Nat.and_two_pow_sub_one_eq_mod]
  rw [R64] at *
  rw [e]
  split
  · rename_i h64
    have : j = 64 := by omega_using [hj, h64]
    subst this
    have := x.isLt
    omega_using [hx]
  · have h0 : 0 ≤ X % 2 ^ 64 := Int.emod_nonneg _ (by decide)
    obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
    have d : ((2 : Int) ^ j) ∣ 2 ^ 64 := ⟨2 ^ (64 - j), by rw [← Int.pow_add]; congr 1; omega_using [hj]⟩
    have e2 : X % 2 ^ j = ((N % 2 ^ j : Nat) : Int) := by
      rw [← Int.emod_emod_of_dvd X d, hN]; push_cast; rfl
    rw [hx, hN, Int.toNat_natCast, e2]
    have := Nat.mod_lt N hp0
    omega_using [hp]

theorem R64.mad {c a b : BitVec 64} {C A B : Int} (hc : R64 c C) (ha : R64 a A) (hb : R64 b B) (h : Bool) :
    R64 (mad52 h c a b) (C + (if h then A % 2 ^ 52 * (B % 2 ^ 52) / 2 ^ 52 else A % 2 ^ 52 * (B % 2 ^ 52) % 2 ^ 52)) := by
  have a0 : 0 ≤ A % 2 ^ 52 := Int.emod_nonneg _ (by decide)
  have b0 : 0 ≤ B % 2 ^ 52 := Int.emod_nonneg _ (by decide)
  obtain ⟨M, hM⟩ := Int.eq_ofNat_of_zero_le a0
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le b0
  have ea : a.toNat % 2 ^ 52 = M := by rw [R64] at ha; omega_using [ha, hM]
  have eb : b.toNat % 2 ^ 52 = N := by rw [R64] at hb; omega_using [hb, hN]
  rw [R64] at *
  rw [mad52_toNat, ea, eb, hM, hN, show ((M : Int) * (N : Int)) = ((M * N : Nat) : Int) by push_cast; rfl]
  generalize M * N = Q
  cases h <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega_using [hc]

theorem R64.slr {x : BitVec 64} {X : Int} (hx : R64 x X) (n j : Nat) :
    R64 ((x <<< n) >>> j) (X * 2 ^ n % 2 ^ 64 / 2 ^ j) := by
  have h1 : R64 (x <<< n) (X * 2 ^ n % 2 ^ 64) := by
    have := hx.shl n
    rw [R64] at this ⊢
    rw [this, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  exact h1.shr (Int.emod_nonneg _ (by decide)) (Int.emod_lt_of_pos _ (by decide)) j

theorem R64.sel {c a b : BitVec 64} {C A B : Int} (hc : R64 c C) (ha : R64 a A) (hb : R64 b B)
    (h0 : -1 ≤ C) (h1 : C ≤ 0) :
    R64 ((c &&& b) ||| (~~~c &&& a)) (if C = 0 then A else B) := by
  by_cases hC : C = 0
  · subst hC
    have e : c = 0#64 := BitVec.eq_of_toNat_eq (by rw [R64] at hc; rw [hc]; rfl)
    subst e
    rw [BitVec.zero_and, BitVec.zero_or, BitVec.not_zero, BitVec.allOnes_and]
    simpa using ha
  · have hC1 : C = -1 := by omega_using [h0, h1, hC]
    subst hC1
    have e : c = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by rw [R64] at hc; rw [hc]; rfl)
    subst e
    rw [BitVec.allOnes_and, BitVec.not_allOnes, BitVec.zero_and, BitVec.or_zero]
    simpa using hb

/-! ## Terms -/

theorem cap_ge {X : Int} {x : Int × Int} (h1 : x.1 ≤ X) (h2 : X ≤ x.2) : X % 2 ^ 52 ≤ cap x := by
  unfold cap
  split
  · rename_i h
    rw [Int.emod_eq_of_lt (by omega_using [h1, h]) (by omega_using [h2, h])]; exact h2
  · have := Int.emod_lt_of_pos X (show (0 : Int) < 2 ^ 52 by decide)
    omega_using []

theorem cap_nonneg {X : Int} {x : Int × Int} (h1 : x.1 ≤ X) (h2 : X ≤ x.2) : 0 ≤ cap x :=
  Int.le_trans (Int.emod_nonneg _ (by decide)) (cap_ge h1 h2)

theorem pow_pos' (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

/-- A term is `T.int` modulo `2⁶⁴`, within `T.iv`. -/
theorem iv_ok {s₀ : State} {B : Bnds} (hB : EnvOK s₀ B) :
    ∀ (t : T) (k : Nat) (iv : Int × Int), k < 4 → t.iv B k = some iv →
      R64 (t.eval s₀ k) (t.int (envOf s₀) k) ∧ iv.1 ≤ t.int (envOf s₀) k ∧ t.int (envOf s₀) k ≤ iv.2 := by
  intro t
  induction t with
  | reg r =>
    intro k iv hk h
    simp only [T.iv, Option.some.injEq] at h
    subst h
    exact ⟨R64.toInt _, hB.v r k hk⟩
  | lit a b c d =>
    intro k iv hk h
    simp only [T.iv, Option.some.injEq] at h
    subst h
    exact ⟨R64.ofNat _, Int.le_refl _, Int.le_refl _⟩
  | ld b d =>
    intro k iv hk h
    simp only [T.iv, Option.some.injEq] at h
    subst h
    refine ⟨?_, hB.m b d k hk⟩
    simp only [T.int, envOf]
    split
    · exact R64.toNat _
    · exact R64.toInt _
  | add a b iha ihb =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    obtain ⟨rb, lb, ub⟩ := ihb k y hk hy
    exact ⟨ra.add rb, Int.add_le_add la lb, Int.add_le_add ua ub⟩
  | sub a b iha ihb =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    obtain ⟨rb, lb, ub⟩ := ihb k y hk hy
    exact ⟨ra.sub rb, Int.sub_le_sub la ub, Int.sub_le_sub ua lb⟩
  | shl a n iha =>
    intro k iv hk h
    simp only [T.iv, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    exact ⟨ra.shl n, Int.mul_le_mul_of_nonneg_right la (Int.le_of_lt (pow_pos' n)),
      Int.mul_le_mul_of_nonneg_right ua (Int.le_of_lt (pow_pos' n))⟩
  | shr a n iha =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    case isFalse => cases h
    rename_i hr
    cases h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    exact ⟨ra.shr (by omega_using [hr, la]) (by omega_using [hr, ua]) n, Int.ediv_le_ediv (pow_pos' n) la, Int.ediv_le_ediv (pow_pos' n) ua⟩
  | sra a n iha =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    case isFalse => cases h
    rename_i hr
    cases h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    exact ⟨ra.sra (by omega_using [hr, la]) (by omega_using [hr, ua]) n, Int.ediv_le_ediv (pow_pos' n) la, Int.ediv_le_ediv (pow_pos' n) ua⟩
  | mask a j0 j1 j2 j3 iha =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    simp only [T.eval, T.int]
    generalize pick4 j0 j1 j2 j3 k = j at h ⊢
    split at h
    case isTrue => cases h
    rename_i hj
    refine ⟨ra.mask (by omega_using [hj]), ?_⟩
    split at h
    · rename_i h64
      cases h
      simp only [h64, ↓reduceIte]; exact ⟨la, ua⟩
    · rename_i h64
      simp only [h64, ↓reduceIte]
      split at h
      · rename_i hr
        cases h
        rw [Int.emod_eq_of_lt (by omega_using [la, hr]) (by omega_using [ua, hr])]; exact ⟨la, ua⟩
      · cases h
        have := Int.emod_lt_of_pos (a.int (envOf s₀) k) (pow_pos' j)
        exact ⟨Int.emod_nonneg _ (Int.ne_of_gt (pow_pos' j)), by omega_using []⟩
  | blend a b m iha ihb =>
    intro k iv hk h
    simp only [T.iv] at h
    simp only [T.eval, T.int]
    split at h
    · rename_i hm; simp only [hm, ↓reduceIte]; exact ihb k iv hk h
    · rename_i hm; simp only [hm]; exact iha k iv hk h
  | perm a o iha =>
    intro k iv hk h
    exact iha (sel4 o k) iv (sel4_lt _ _) h
  | mad hh c a b ihc iha ihb =>
    intro k iv hk h
    cases hh with
    | false =>
      simp only [T.iv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      obtain ⟨rc, lc, uc⟩ := ihc k x hk hx
      obtain ⟨ra, -, -⟩ := iha k y hk hy
      obtain ⟨rb, -, -⟩ := ihb k z hk hz
      refine ⟨rc.mad ra rb false, ?_, ?_⟩
      · have := Int.emod_nonneg (a.int (envOf s₀) k % 2 ^ 52 * (b.int (envOf s₀) k % 2 ^ 52))
          (show (2 : Int) ^ 52 ≠ 0 by decide)
        simp only [T.int]; omega_using [lc]
      · have := Int.emod_lt_of_pos (a.int (envOf s₀) k % 2 ^ 52 * (b.int (envOf s₀) k % 2 ^ 52))
          (show (0 : Int) < 2 ^ 52 by decide)
        simp only [T.int]; omega_using [uc]
    | true =>
      simp only [T.iv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      obtain ⟨rc, lc, uc⟩ := ihc k x hk hx
      obtain ⟨ra, la, ua⟩ := iha k y hk hy
      obtain ⟨rb, lb, ub⟩ := ihb k z hk hz
      have a0 : 0 ≤ a.int (envOf s₀) k % 2 ^ 52 := Int.emod_nonneg _ (by decide)
      have b0 : 0 ≤ b.int (envOf s₀) k % 2 ^ 52 := Int.emod_nonneg _ (by decide)
      have hp : a.int (envOf s₀) k % 2 ^ 52 * (b.int (envOf s₀) k % 2 ^ 52) ≤ cap y * cap z :=
        Int.mul_le_mul (cap_ge la ua) (cap_ge lb ub) b0 (cap_nonneg la ua)
      refine ⟨rc.mad ra rb true, ?_, ?_⟩
      · have := Int.ediv_nonneg (Int.mul_nonneg a0 b0) (show (0 : Int) ≤ 2 ^ 52 by decide)
        simp only [T.int]; omega_using [lc, this]
      · have := Int.ediv_le_ediv (show (0 : Int) < 2 ^ 52 by decide) hp
        simp only [T.int]; omega_using [uc, hp]
  | slr a n j iha =>
    intro k iv hk h
    simp only [T.iv, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨ra, -, -⟩ := iha k x hk hx
    have h0 : 0 ≤ a.int (envOf s₀) k * 2 ^ n % 2 ^ 64 := Int.emod_nonneg _ (by decide)
    have h1 : a.int (envOf s₀) k * 2 ^ n % 2 ^ 64 ≤ 2 ^ 64 - 1 := by
      have := Int.emod_lt_of_pos (a.int (envOf s₀) k * 2 ^ n) (show (0 : Int) < 2 ^ 64 by decide)
      omega_using []
    exact ⟨ra.slr n j, Int.ediv_nonneg h0 (Int.le_of_lt (pow_pos' j)), Int.ediv_le_ediv (pow_pos' j) h1⟩
  | sel c a b ihc iha ihb =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, h⟩ := h
    split at h
    case isFalse => cases h
    rename_i hr
    cases h
    obtain ⟨rc, lc, uc⟩ := ihc k x hk hx
    obtain ⟨ra, la, ua⟩ := iha k y hk hy
    obtain ⟨rb, lb, ub⟩ := ihb k z hk hz
    refine ⟨rc.sel ra rb (by omega_using [hr, lc]) (by omega_using [hr, uc]), ?_⟩
    simp only [T.int]
    split <;> omega_arith

end

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Bignum.X86_64.Ifma (vi vreg_vi vi_vreg qv)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)
open VG.Proof.Weierstrass (Unch)

def klit (c : K4) : T := .lit c.w0 c.w1 c.w2 c.w3

/-- The operations as terms: what `VSym.run` makes of the instructions
`allocCuts` writes for each. -/
def tops : Ops Id T where
  add a b := .add a b
  sub a b := .sub a b
  sll a n := .shl a n
  srl a n := shrOf a n
  sra a n := .sra a n
  addc a c := .add a (klit c)
  andc a c := match maskOf (klit c) with
    | some j => .mask a j.1 j.2.1 j.2.2.1 j.2.2.2
    | none => a
  perm a o := .perm a o
  blend a b m := selOf (klit (K4.lanes m)) a b
  madd h acc a b := .mad h (acc.getD (.lit 0 0 0 0)) a b
  maddc h acc a c := .mad h (acc.getD (.lit 0 0 0 0)) a (klit c)
  slr a n k := .slr a n k
  sel c a b := selOf c a b
  zero := .lit 0 0 0 0
  const c := klit c

/-- What the blocks run with: their constants at `r10`; the words of a
point's three coordinates at `rcx` and of two more field elements at `rdx`,
and the mask of an entry's sign at `r9`; and the working space at `rdi`, to the end of the slots, which
are from `5056` of it. -/
def par : Par :=
  ⟨.r10, poolLit.flatMap fun k => [k.w0, k.w1, k.w2, k.w3],
    fun r => if r = .rcx then 96 else if r = .rdx then 64 else if r = .r9 then 32 else 0, 5920, 5056, 0⟩

/-- The offset of a slot in the working space. -/
def slotOff (i : Nat) : Nat := cfg.sbase + 32 * i

/-- A place, as a term of the state a piece starts from. -/
def leafOf : Loc → T
  | .reg r => .reg r
  | .slot i => .ld .rdi (slotOff i)

/-- The term in a place after a run. -/
def termAt (σ : VSym) : Loc → T
  | .reg r => σ.reg r
  | .slot i => look σ.st (slotOff i)

/-- A place a piece may leave a value in. -/
def locOk : Loc → Bool
  | .reg r => decide (r < 32)
  | .slot i => decide (slotOff i + 32 ≤ par.win)

/-- Quadword `k` of a place. -/
def lanesAt (s : State) : Loc → Nat → BitVec 64
  | .reg r, k => qv s (vreg r) k
  | .slot i, k => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (slotOff i + 8 * k)) 64

theorem leafOf_eval (s : State) (l : Loc) (k : Nat) : (leafOf l).eval s k = lanesAt s l k := by
  cases l <;> rfl

def group5 : List T → List (F5 T)
  | a :: b :: c :: d :: e :: rest => ⟨a, b, c, d, e⟩ :: group5 rest
  | _ => []

/-- The terms of a stage's results. -/
def segT (seg : Seg Id T) (ins : List (F5 T)) : List T := (Id.run (seg ins)).flatMap F5.toList

/-- The bytes of the slots the blocks store to, nine: the working space past them, to `par.win`, is
only read. -/
abbrev slotsLen : Nat := 288

/-- The code of a stage computes its terms, into the places `outs`, and stores only into the first
`w` bytes of the slots. -/
def chkSegW (w : Nat) (code : List Instr) (ins : List (F5 T)) (seg : Seg Id T) (outs : List Loc) : Bool :=
  match VSym.init.run par code with
  | some σ => decide (outs.map (termAt σ) = segT seg ins) && outs.all locOk &&
    σ.st.all fun e => decide (cfg.sbase ≤ e.1 ∧ e.1 + 32 ≤ cfg.sbase + w)
  | none => false

/-- `chkSegW`, for the first nine slots. -/
abbrev chkSeg (code : List Instr) (ins : List (F5 T)) (seg : Seg Id T) (outs : List Loc) : Bool :=
  chkSegW slotsLen code ins seg outs

/-- Stage `j` of a block, from the terms `ins` at its start, its last stage's values into `fin`. -/
def chkStage (pieces : List (List Instr)) (locs : List (List Loc)) (segs : List (Seg Id T)) (ins : List (F5 T))
    (fin : List Loc) (j : Nat) : Bool :=
  let i := if j = 0 then ins else group5 ((locs.getD (j - 1) []).map leafOf)
  let o := if j + 1 = segs.length then fin else locs.getD j []
  chkSeg (pieces.getD j []) i (segs.getD j (fun _ => pure [])) o

theorem slotOff_mod (i : Nat) : slotOff i % 32 = 0 := by
  simp only [slotOff, cfg]; omega_using []

/-- A place after a run holds its term. -/
theorem termAt_ok {σ : VSym} {s₀ s : State} (h : SRel par σ s₀ s) {l : Loc} (hl : locOk l = true) {k : Nat}
    (hk : k < 4) : lanesAt s l k = (termAt σ l).eval s₀ k := by
  cases l with
  | reg r =>
    simp only [locOk, decide_eq_true_eq] at hl
    have := h.reg (vreg r) k hk
    rw [vi_vreg r hl] at this
    exact this
  | slot i =>
    simp only [locOk, decide_eq_true_eq] at hl
    simp only [lanesAt, termAt]
    rw [h.mem, h.gpr]
    exact stores_look (by decide) (slotOff_mod i) hl hk σ.st h.al

/-- Stores from `lo` to `hi` change nothing else. -/
theorem stores_unch_hi (s₀ : State) (lo hi : Nat) :
    ∀ (st : List (Nat × T)), (∀ e ∈ st, (lo ≤ e.1 ∧ e.1 + 32 ≤ hi) ∧ e.1 + 32 ≤ par.win) →
      Unch (s₀.gpr .rdi) [(lo, hi - lo)] s₀.mem (stores s₀ st)
  | [], _ => Unch.refl _ _ _
  | (e, t) :: st, he => by
    have he0 := he (e, t) List.mem_cons_self
    intro x hx
    have h1 := hx (lo, hi - lo) (List.mem_singleton.2 rfl)
    simp only [stores]
    rw [writeW_byte_off _ _ _ _ ?_]
    · exact stores_unch_hi s₀ lo hi st (fun y hy => he y (List.mem_cons_of_mem _ hy)) x hx
    · simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.reduceDiv]
      have := (x - s₀.gpr .rdi).isLt
      have hw : par.win = 5920 := rfl
      simp only [VG.Proof.Mont.ofs] at h1
      omega_using [he0, h1, hw]

/-- What a piece does: every quadword of every place of its results is its
term, of the state before; nothing else of the state changes but vector
registers and the first nine slots of the working space. -/
theorem stage_wp {w : Nat} {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSegW w c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, w)] s₀.mem s.mem ∧
      ∀ (j : Nat) (l : Loc) (t : T), outs[j]? = some l → (segT seg ins)[j]? = some t →
        ∀ k, k < 4 → lanesAt s l k = t.eval s₀ k := by
  unfold chkSegW at h
  split at h
  case h_2 => cases h
  rename_i σ hσ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine WP.mono (srun_ok hc c (SRel.init par s₀) hσ) fun s hs => ⟨⟨σ, hs⟩, ?_, fun j l t hl ht k hk => ?_⟩
  · rw [hs.mem]
    have := stores_unch_hi s₀ cfg.sbase (cfg.sbase + w) σ.st fun e he => by
      have := List.all_eq_true.1 h.2 e he
      exact ⟨by simpa using this, (hs.al e he).2⟩
    rwa [Nat.add_sub_cancel_left] at this
  · have hok : locOk l = true := List.all_eq_true.1 h.1.2 l (List.mem_of_getElem? hl)
    rw [← h.1.1, List.getElem?_map, hl] at ht
    cases ht
    exact termAt_ok hs hok hk

/-- Quadword `k` of a place, as a signed integer. -/
def ints (s : State) (l : Loc) (k : Nat) : Int := (lanesAt s l k).toInt

theorem envOf_reg (s : State) (r k : Nat) : (envOf s).v r k = ints s (.reg r) k := rfl

theorem envOf_slot (s : State) (i k : Nat) : (envOf s).m .rdi (slotOff i) k = ints s (.slot i) k := rfl

/-- `stage_wp`, for integers: the quadwords of a place whose term has bounds
(`T.iv`) within 64 signed bits are the term's integer. -/
theorem stage_int {w : Nat} {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSegW w c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, w)] s₀.mem s.mem ∧
      ∀ (j : Nat) (l : Loc) (t : T), outs[j]? = some l → (segT seg ins)[j]? = some t →
        ∀ k, k < 4 → ∀ iv, t.iv B k = some iv → -2 ^ 63 ≤ iv.1 → iv.2 < 2 ^ 63 →
          ints s l k = t.int (envOf s₀) k ∧ iv.1 ≤ t.int (envOf s₀) k ∧ t.int (envOf s₀) k ≤ iv.2 := by
  refine WP.mono (stage_wp h hc) fun s ⟨hσ, hu, hs⟩ => ⟨hσ, hu, fun j l t hl ht k hk iv hiv h0 h1 => ?_⟩
  obtain ⟨r, lo, hi⟩ := iv_ok hB t k iv hk hiv
  rw [ints, hs j l t hl ht k hk]
  exact ⟨r.int (by omega_using [h0, lo]) (by omega_using [h1, hi]), lo, hi⟩

end VG.Proof.P256.X86_64.Ifma

end

end

/-!
# P-256 on x86-64 with AVX512_IFMA: sums, differences and choices of field vectors

What the terms of the operations between the products (`fadd`, `fsub`,
`fshl`, `fperm`, `fblend`, the masked sums and differences, `fbias`) are as
numbers (`vI`), lane by lane.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## The field's operations, as integers

What the terms of `norm`, `mulCore` and `sqrCore` (read with `tops`) are as
integers (`T.int`), for any terms they are given.
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

theorem pick4_same {α : Type} (a : α) (k : Nat) : pick4 a a a a k = a := by
  unfold pick4; split <;> rfl

theorem maskOf_mask : maskOf (klit kMask) = some (52, 52, 52, 52) := by decide
theorem maskOf_m48 : maskOf (klit kM48) = some (48, 48, 48, 48) := by decide

theorem andc_mask (a : T) : tops.andc a kMask = .mask a 52 52 52 52 := by
  simp only [tops, maskOf_mask]
theorem andc_m48 (a : T) : tops.andc a kM48 = .mask a 48 48 48 48 := by
  simp only [tops, maskOf_m48]

theorem mask52_int (a : T) (E : Env) (k : Nat) : (T.mask a 52 52 52 52).int E k = a.int E k % 2 ^ 52 := by
  simp only [T.int, pick4_same, Nat.reduceLeDiff, ↓reduceIte]
theorem mask48_int (a : T) (E : Env) (k : Nat) : (T.mask a 48 48 48 48).int E k = a.int E k % 2 ^ 48 := by
  simp only [T.int, pick4_same, Nat.reduceLeDiff, ↓reduceIte]

/-- The limbs of a field vector's lane `k`, as integers. -/
def li (E : Env) (k : Nat) (v : F5 T) : Int × Int × Int × Int × Int :=
  (v.l0.int E k, v.l1.int E k, v.l2.int E k, v.l3.int E k, v.l4.int E k)

/-- The number lane `k` of a field vector stands for. -/
def vI (E : Env) (k : Nat) (v : F5 T) : Int :=
  val5 (v.l0.int E k) (v.l1.int E k) (v.l2.int E k) (v.l3.int E k) (v.l4.int E k)

/-- `norm`, as integers. -/
theorem norm_int (v : F5 T) (E : Env) (k : Nat) :
    li E k (Id.run (norm tops v)) =
      normI (v.l0.int E k) (v.l1.int E k) (v.l2.int E k) (v.l3.int E k) (v.l4.int E k) := by
  simp only [norm, Id.run, bind, pure, andc_mask, andc_m48, li, normI]
  simp only [tops, T.int, pick4_same, Nat.reduceLeDiff, ↓reduceIte]

/-- The reduction, as integers; its first column is not a shift left (which `shrOf` would take
with the shift right of it). -/
theorem reduce_int (d t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : T) (h0 : shrOf t0 52 = .shr t0 52) (E : Env) (k : Nat) :
    li E k (Id.run (reduce tops d [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9])) =
      reduceI [t0.int E k, t1.int E k, t2.int E k, t3.int E k, t4.int E k, t5.int E k, t6.int E k, t7.int E k, t8.int E k, t9.int E k] := by
  simp only [reduce, redStep, Id.run, bind, pure, andc_mask, List.getD_cons_zero, List.getD_cons_succ,
    List.set_cons_zero, List.set_cons_succ, li, reduceI, redI]
  simp only [tops, Option.getD_some]
  simp only [h0]
  have c1 : ((2 ^ 36 : Nat) : Int) = 2 ^ 36 := by decide
  have c2 : ((2 ^ 48 - 2 ^ 16 : Nat) : Int) = 2 ^ 48 - 2 ^ 16 := by decide
  simp only [shrOf, T.int, klit, k36, kP4, K4.all, pick4_same, lo52, hi52, Nat.reduceLeDiff, ↓reduceIte, c1, c2]

/-- The columns of a product. -/
def mulColsT (a b : F5 T) : List T :=
  [.mad false (.lit 0 0 0 0) a.l0 b.l0,
    .mad false (.mad false (.mad true (.lit 0 0 0 0) a.l0 b.l0) a.l1 b.l0) a.l0 b.l1,
    .add (.mad false (.mad false (.mad true (.lit 0 0 0 0) a.l1 b.l0) a.l1 b.l1) a.l0 b.l2) (.mad false (.mad true (.lit 0 0 0 0) a.l0 b.l1) a.l2 b.l0),
    .add (.add (.mad false (.mad false (.mad true (.lit 0 0 0 0) a.l1 b.l1) a.l2 b.l1) a.l0 b.l3) (.mad false (.mad true (.lit 0 0 0 0) a.l2 b.l0) a.l1 b.l2)) (.mad false (.mad true (.lit 0 0 0 0) a.l0 b.l2) a.l3 b.l0),
    .add (.add (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l2 b.l1) a.l3 b.l0) a.l1 b.l3) (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l1 b.l2) a.l0 b.l3) a.l4 b.l0)) (.mad false (.mad false (.mad false (.lit 0 0 0 0) a.l2 b.l2) a.l3 b.l1) a.l0 b.l4),
    .add (.add (.mad true (.mad false (.mad true (.lit 0 0 0 0) a.l2 b.l2) a.l3 b.l2) a.l0 b.l4) (.mad false (.mad false (.mad true (.lit 0 0 0 0) a.l3 b.l1) a.l2 b.l3) a.l4 b.l1)) (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l1 b.l3) a.l4 b.l0) a.l1 b.l4),
    .add (.add (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l3 b.l2) a.l4 b.l1) a.l2 b.l4) (.mad true (.mad true (.lit 0 0 0 0) a.l2 b.l3) a.l1 b.l4)) (.mad false (.mad false (.lit 0 0 0 0) a.l3 b.l3) a.l4 b.l2),
    .add (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l3 b.l3) a.l2 b.l4) a.l3 b.l4) (.mad false (.mad true (.lit 0 0 0 0) a.l4 b.l2) a.l4 b.l3),
    .mad false (.mad true (.mad true (.lit 0 0 0 0) a.l4 b.l3) a.l3 b.l4) a.l4 b.l4,
    .mad true (.lit 0 0 0 0) a.l4 b.l4]

theorem mulCols_eq (a b : F5 T) : Id.run (mulCols tops a b) = mulColsT a b := rfl

/-- The columns of a square. -/
def sqrColsT (a : F5 T) : List T :=
  [.mad false (.lit 0 0 0 0) a.l0 a.l0,
    .mad true (.add (.mad false (.lit 0 0 0 0) a.l0 a.l1) (.mad false (.lit 0 0 0 0) a.l0 a.l1)) a.l0 a.l0,
    .mad false (.add (.mad false (.mad true (.lit 0 0 0 0) a.l0 a.l1) a.l0 a.l2) (.mad false (.mad true (.lit 0 0 0 0) a.l0 a.l1) a.l0 a.l2)) a.l1 a.l1,
    .mad true (.add (.mad false (.mad false (.mad true (.lit 0 0 0 0) a.l0 a.l2) a.l1 a.l2) a.l0 a.l3) (.mad false (.mad false (.mad true (.lit 0 0 0 0) a.l0 a.l2) a.l1 a.l2) a.l0 a.l3)) a.l1 a.l1,
    .mad false (.add (.add (.mad false (.mad true (.lit 0 0 0 0) a.l1 a.l2) a.l1 a.l3) (.mad false (.mad true (.lit 0 0 0 0) a.l0 a.l3) a.l0 a.l4)) (.add (.mad false (.mad true (.lit 0 0 0 0) a.l1 a.l2) a.l1 a.l3) (.mad false (.mad true (.lit 0 0 0 0) a.l0 a.l3) a.l0 a.l4))) a.l2 a.l2,
    .mad true (.add (.add (.mad true (.mad true (.lit 0 0 0 0) a.l1 a.l3) a.l0 a.l4) (.mad false (.mad false (.lit 0 0 0 0) a.l2 a.l3) a.l1 a.l4)) (.add (.mad true (.mad true (.lit 0 0 0 0) a.l1 a.l3) a.l0 a.l4) (.mad false (.mad false (.lit 0 0 0 0) a.l2 a.l3) a.l1 a.l4))) a.l2 a.l2,
    .mad false (.add (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l2 a.l3) a.l1 a.l4) a.l2 a.l4) (.mad false (.mad true (.mad true (.lit 0 0 0 0) a.l2 a.l3) a.l1 a.l4) a.l2 a.l4)) a.l3 a.l3,
    .mad true (.add (.mad false (.mad true (.lit 0 0 0 0) a.l2 a.l4) a.l3 a.l4) (.mad false (.mad true (.lit 0 0 0 0) a.l2 a.l4) a.l3 a.l4)) a.l3 a.l3,
    .mad false (.add (.mad true (.lit 0 0 0 0) a.l3 a.l4) (.mad true (.lit 0 0 0 0) a.l3 a.l4)) a.l4 a.l4,
    .mad true (.lit 0 0 0 0) a.l4 a.l4]

theorem sqrCols_eq (a : F5 T) : Id.run (sqrCols tops a) = sqrColsT a := rfl

theorem mulCols_int (a b : F5 T) (E : Env) (k : Nat) :
    (mulColsT a b).map (fun t => t.int E k) = mulColsI (a.l0.int E k) (a.l1.int E k) (a.l2.int E k) (a.l3.int E k) (a.l4.int E k) (b.l0.int E k) (b.l1.int E k) (b.l2.int E k) (b.l3.int E k) (b.l4.int E k) := by
  have z : ((0 : Nat) : Int) = 0 := rfl
  simp only [mulColsT, List.map_cons, List.map_nil, T.int, pick4_same, z, mulColsI, lo52, hi52]

theorem sqrCols_int (a : F5 T) (E : Env) (k : Nat) :
    (sqrColsT a).map (fun t => t.int E k) = sqrColsI (a.l0.int E k) (a.l1.int E k) (a.l2.int E k) (a.l3.int E k) (a.l4.int E k) := by
  have z : ((0 : Nat) : Int) = 0 := rfl
  simp only [sqrColsT, List.map_cons, List.map_nil, T.int, pick4_same, z, sqrColsI, lo52, hi52]

/-- The limbs of lane `k` are in `[0, 2⁵²)`. -/
def Carried (E : Env) (k : Nat) (v : F5 T) : Prop :=
  (0 ≤ v.l0.int E k ∧ v.l0.int E k < 2 ^ 52) ∧ (0 ≤ v.l1.int E k ∧ v.l1.int E k < 2 ^ 52) ∧
    (0 ≤ v.l2.int E k ∧ v.l2.int E k < 2 ^ 52) ∧ (0 ≤ v.l3.int E k ∧ v.l3.int E k < 2 ^ 52) ∧
    (0 ≤ v.l4.int E k ∧ v.l4.int E k < 2 ^ 52)

theorem reduceI_valL (t : List Int) (ht : t.length = 10) :
    let o := reduceI t
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧ val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 * 2 ^ 260 = val10L t + M * pI := by
  match t, ht with
  | [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9], _ => exact reduceI_val t0 t1 t2 t3 t4 t5 t6 t7 t8 t9

theorem mulCore_li (a b : F5 T) (E : Env) (k : Nat) :
    li E k (Id.run (mulCore tops a b)) = reduceI ((mulColsT a b).map fun t => t.int E k) := by
  have := mulCols_eq a b
  simp only [Id.run] at this
  simp only [mulCore, Id.run, bind, this, mulColsT, List.map_cons, List.map_nil]
  exact reduce_int _ _ _ _ _ _ _ _ _ _ _ rfl E k

theorem sqrCore_li (a : F5 T) (E : Env) (k : Nat) :
    li E k (Id.run (sqrCore tops a)) = reduceI ((sqrColsT a).map fun t => t.int E k) := by
  have := sqrCols_eq a
  simp only [Id.run] at this
  simp only [sqrCore, Id.run, bind, this, sqrColsT, List.map_cons, List.map_nil]
  exact reduce_int _ _ _ _ _ _ _ _ _ _ _ rfl E k

theorem vI_li (E : Env) (k : Nat) (v : F5 T) :
    vI E k v = val5 (li E k v).1 (li E k v).2.1 (li E k v).2.2.1 (li E k v).2.2.2.1 (li E k v).2.2.2.2 := rfl

/-- A product of carried lanes, times `2²⁶⁰`, is the product of the numbers plus a multiple of `p`. -/
theorem mulCore_val (a b : F5 T) (E : Env) (k : Nat) (ha : Carried E k a) (hb : Carried E k b) :
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧
      vI E k (Id.run (mulCore tops a b)) * 2 ^ 260 = vI E k a * vI E k b + M * pI := by
  obtain ⟨M, h0, h1, h2⟩ := reduceI_valL ((mulColsT a b).map fun t => t.int E k)
    (by simp only [mulColsT, List.map_cons, List.map_nil, List.length_cons, List.length_nil])
  rw [mulCols_int, mulColsI_val ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
    hb.2.2.2.2, ← mulCols_int, ← mulCore_li] at h2
  rw [vI_li]
  exact ⟨M, h0, h1, h2⟩

/-- A square of carried lanes, likewise. -/
theorem sqrCore_val (a : F5 T) (E : Env) (k : Nat) (ha : Carried E k a) :
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧
      vI E k (Id.run (sqrCore tops a)) * 2 ^ 260 = vI E k a * vI E k a + M * pI := by
  obtain ⟨M, h0, h1, h2⟩ := reduceI_valL ((sqrColsT a).map fun t => t.int E k)
    (by simp only [sqrColsT, List.map_cons, List.map_nil, List.length_cons, List.length_nil])
  rw [sqrCols_int, sqrColsI_val ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2, ← sqrCols_int, ← sqrCore_li] at h2
  rw [vI_li]
  exact ⟨M, h0, h1, h2⟩

end

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

theorem blendOf_lanes : ∀ m < 16, blendOf (klit (K4.lanes m)) = some m := by decide

theorem maskOf_lanes : ∀ m < 16, maskOf (klit (K4.lanes m)) =
    some (if m.testBit 0 then 64 else 0, if m.testBit 1 then 64 else 0, if m.testBit 2 then 64 else 0,
      if m.testBit 3 then 64 else 0) := by decide

theorem tops_blend (a b : T) {m : Nat} (hm : m < 16) : tops.blend a b m = .blend a b m := by
  simp only [tops, selOf, blendOf_lanes m hm]

theorem tops_andl (a : T) {m : Nat} (hm : m < 16) :
    tops.andc a (K4.lanes m) = .mask a (if m.testBit 0 then 64 else 0) (if m.testBit 1 then 64 else 0)
      (if m.testBit 2 then 64 else 0) (if m.testBit 3 then 64 else 0) := by
  simp only [tops, maskOf_lanes m hm]

/-- A term masked to the lanes of `m`. -/
theorem andl_int (a : T) {m : Nat} (hm : m < 16) (E : Env) {k : Nat} (hk : k < 4) :
    (tops.andc a (K4.lanes m)).int E k = if m.testBit k then a.int E k else 0 := by
  rw [tops_andl a hm]
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp only [T.int, pick4] <;> split <;>
    simp_all [Int.emod_one]

theorem vI_fadd (a b : F5 T) (E : Env) (k : Nat) : vI E k (fadd tops a b) = vI E k a + vI E k b := by
  simp only [fadd, F5.zipM, bind, pure, tops, vI, T.int, val5]
  omega_using []

theorem vI_fsub (a b : F5 T) (E : Env) (k : Nat) : vI E k (fsub tops a b) = vI E k a - vI E k b := by
  simp only [fsub, F5.zipM, bind, pure, tops, vI, T.int, val5]
  omega_using []

theorem vI_fshl (a : F5 T) (n : Nat) (E : Env) (k : Nat) :
    vI E k (fshl tops a n) = vI E k a * 2 ^ n := by
  by_cases h : n = 1
  · subst h
    simp only [fshl, F5.mapM, bind, pure, tops, vI, T.int, val5, ↓reduceIte]
    omega_using []
  · simp only [fshl, F5.mapM, bind, pure, tops, vI, T.int, val5, h, ↓reduceIte]
    generalize (2 : Int) ^ n = w
    grind

theorem vI_fperm (a : F5 T) (i0 i1 i2 i3 : Nat) (E : Env) (k : Nat) :
    vI E k (fperm tops a i0 i1 i2 i3) = vI E (sel4 (i0 + 4 * i1 + 16 * i2 + 64 * i3) k) a := by
  simp only [fperm, F5.mapM, bind, pure, tops, vI, T.int]

theorem vI_fblend (a b : F5 T) {m : Nat} (hm : m < 16) (E : Env) (k : Nat) :
    vI E k (fblend tops a b m) = if m.testBit k then vI E k b else vI E k a := by
  simp only [fblend, F5.zipM, bind, pure, tops_blend _ _ hm, vI, T.int]
  split <;> rfl

theorem vI_fmadd (acc b : F5 T) {m : Nat} (hm : m < 16) (E : Env) {k : Nat} (hk : k < 4) :
    vI E k (fmadd tops acc b m) = vI E k acc + if m.testBit k then vI E k b else 0 := by
  have e (x y : T) : (tops.add x (tops.andc y (K4.lanes m))).int E k =
      x.int E k + if m.testBit k then y.int E k else 0 := by
    rw [← andl_int y hm E hk]; rfl
  simp only [fmadd, F5.zipM, bind, pure, vI, e, val5]
  split <;> omega_using []

theorem vI_fmsub (acc b : F5 T) {m : Nat} (hm : m < 16) (E : Env) {k : Nat} (hk : k < 4) :
    vI E k (fmsub tops acc b m) = vI E k acc - if m.testBit k then vI E k b else 0 := by
  have e (x y : T) : (tops.sub x (tops.andc y (K4.lanes m))).int E k =
      x.int E k - if m.testBit k then y.int E k else 0 := by
    rw [← andl_int y hm E hk]; rfl
  simp only [fmsub, F5.zipM, bind, pure, vI, e, val5]
  split <;> omega_using []

theorem vI_fmrsub (acc a : F5 T) {m : Nat} (hm : m < 16) (E : Env) (k : Nat) :
    vI E k (fmrsub tops acc a m) = if m.testBit k then vI E k a - vI E k acc else vI E k acc := by
  have e (x y : T) : (tops.blend x (tops.sub y x) m).int E k =
      if m.testBit k then y.int E k - x.int E k else x.int E k := by
    rw [tops_blend _ _ hm]; rfl
  simp only [fmrsub, F5.zipM, bind, pure, vI, e, val5]
  split <;> omega_using []

theorem limbOf_val (v : Nat) :
    val5 (limbOf v 0 : Nat) (limbOf v 1 : Nat) (limbOf v 2 : Nat) (limbOf v 3 : Nat) (limbOf v 4 : Nat) = (v : Int) := by
  simp only [limbOf, val5, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul]
  omega_using []

theorem pN_eq : (pN : Int) = pI := by decide

theorem vI_fbias (a : F5 T) (k0 k1 k2 k3 : Nat) (E : Env) {k : Nat} (hk : k < 4) :
    vI E k (fbias tops a k0 k1 k2 k3) = vI E k a + (pick4 k0 k1 k2 k3 k : Nat) * pI := by
  have e (x : T) (i : Nat) : (tops.addc x (biasK k0 k1 k2 k3 i)).int E k =
      x.int E k + (limbOf (pick4 k0 k1 k2 k3 k * pN) i : Nat) := by
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
  have := limbOf_val (pick4 k0 k1 k2 k3 k * pN)
  rw [Int.natCast_mul, pN_eq] at this
  simp only [fbias, bind, pure, vI, e]
  simp only [val5] at this ⊢
  omega_using [this]

theorem vI_fneg (a : F5 T) (E : Env) (k : Nat) : vI E k (fneg tops a) = -vI E k a := by
  have z : ((0 : Nat) : Int) = 0 := rfl
  simp only [fneg, F5.mapM, bind, pure, tops, vI, T.int, pick4_same, z, val5]
  omega_using []

theorem vI_fsel (c : T) (hc : blendOf c = none) (a b : F5 T) (E : Env) (k : Nat) :
    vI E k (fsel tops c a b) = if c.int E k = 0 then vI E k a else vI E k b := by
  simp only [fsel, F5.zipM, bind, pure, tops, selOf, hc, vI, T.int]
  split <;> rfl

/-- The simp set that evaluates the number of a lane of sums, differences and choices of field vectors. -/
macro "glue_simp" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [$ds,*, Id.run, bind, pure, vI_fbias, vI_fblend, vI_fmadd, vI_fmsub, vI_fmrsub, vI_fperm,
    vI_fshl, vI_fadd, vI_fsub, sel4, pick4, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceDiv,
    Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceBEq, Nat.reduceBNe,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Bool.false_eq_true,
    reduceCtorEq])

/-! ## `norm` -/

theorem iv_add_right {B : Bnds} {a b : T} {k : Nat} {iv : Int × Int} (h : (T.add a b).iv B k = some iv) :
    ∃ y, b.iv B k = some y := by
  simp only [T.iv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, _, y, hy, _⟩ := h
  exact ⟨y, hy⟩

theorem iv_sra {B : Bnds} {a : T} {n k : Nat} {iv : Int × Int} (h : (T.sra a n).iv B k = some iv) :
    ∃ x, a.iv B k = some x ∧ -2 ^ 63 ≤ x.1 ∧ x.2 < 2 ^ 63 := by
  simp only [T.iv, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, h⟩ := h
  split at h
  · rename_i hr; exact ⟨x, hx, hr⟩
  · cases h

/-- What the last carry of `norm` is taken from. -/
def normY3 (v : F5 T) : T :=
  .add (.sub v.l3 (.shl (.sra v.l4 48) 36))
    (.sra (.add v.l2 (.sra (.add (.sub v.l1 (.shl (.sra v.l4 48) 44)) (.sra (.add v.l0 (.sra v.l4 48)) 52)) 52)) 52)

theorem norm_l4 (v : F5 T) :
    (Id.run (norm tops v)).l4 = .add (.add (.mask v.l4 48 48 48 48) (.shl (.sra v.l4 48) 16)) (.sra (normY3 v) 52) := by
  simp only [norm, Id.run, bind, pure, tops, maskOf_m48, normY3]

/-- `norm` of a lane whose number is in `[0, 2²⁶⁸)` and whose top limb has
bounds: carried, the number less a multiple of `p`, below `2²⁵⁶ + 2²³⁸`. -/
theorem norm_carried {s₀ : State} {B : Bnds} (hB : EnvOK s₀ B) (v : F5 T) {k : Nat} (hk : k < 4) {iv : Int × Int}
    (h : (Id.run (norm tops v)).l4.iv B k = some iv)
    (h0 : 0 ≤ vI (envOf s₀) k v) (h1 : vI (envOf s₀) k v < 2 ^ 268) :
    Carried (envOf s₀) k (Id.run (norm tops v)) ∧
      vI (envOf s₀) k (Id.run (norm tops v)) = vI (envOf s₀) k v - v.l4.int (envOf s₀) k / 2 ^ 48 * pI ∧
      0 ≤ vI (envOf s₀) k (Id.run (norm tops v)) ∧ vI (envOf s₀) k (Id.run (norm tops v)) < 2 ^ 256 + 2 ^ 238 := by
  rw [norm_l4] at h
  obtain ⟨y, hy⟩ := iv_add_right h
  obtain ⟨x, hx, r0, r1⟩ := iv_sra hy
  obtain ⟨-, lo, hi⟩ := iv_ok hB (normY3 v) k x hk hx
  have r3 : -2 ^ 63 ≤ (normY3 v).int (envOf s₀) k ∧ (normY3 v).int (envOf s₀) k < 2 ^ 63 := ⟨by omega_using [r0, lo], by omega_using [r1, hi]⟩
  simp only [normY3, T.int] at r3
  have := normI_carried r3 h0 h1
  rw [← norm_int] at this
  exact this

end VG.Proof.P256.X86_64.Ifma

end

end

/-!
# P-256 on x86-64 with AVX512_IFMA: a stage's piece of code

`cut_step`: what a stage's piece of code does to what is known between the
stages. From bounds of what it starts from (`EnvOK`), the numbers (`vI`) of
the lanes of the field vectors in the places of its results are those of the
stage's terms in the state before, and are carried where those are; and the
bounds the next stage starts from hold (`bndsOf`), which are the bounds of
the terms (`T.iv`) but for the carried lanes `ovs`, known by their number.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## The bounds between the stages

For each stage of each block: the bounds of its terms' limbs (`…IV`), lane
by lane, from the bounds before it, which the kernel computes (`T.iv`,
`StageFacts.lean`); and the bounds its results are known to have (`…BT`), which are
those but for carried results, whose top limb's bounds are from their value
(`normI_lt`).
-/

section

/-!
## Between the stages of a block

Between two stages the values a block still needs are in the places `L`
(five for each field vector, `Code.lean`). What is known of them is said of
the integers of their limbs, lane by lane (`tab`), and passes from the
terms of a stage, in the state before its piece of code, to the places
after it (`stage_tab`), for the lanes whose terms have bounds within 64
signed bits (`ivWithin`, which the kernel evaluates).
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Bignum.X86_64.Ifma (qv)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)
open VG.Proof.Weierstrass (Unch)

/-- A field vector of no meaning. -/
def zero5 : F5 T := F5.rep (.lit 0 0 0 0)

/-- Limb `i` of lane `k` of field vector `j`, as an integer. -/
def tab (E : Env) (xs : List (F5 T)) (j i k : Nat) : Int := ((xs.getD j zero5).get i).int E k

/-- The field vectors in the places `L`, as terms of the state. -/
def leaves (L : List Loc) : List (F5 T) := group5 (L.map leafOf)

/-- Bounds for the limbs of each lane of each field vector, where known. -/
abbrev BT := List (List (Option (Int × Int)))

def BT.get (bt : BT) (j k : Nat) : Option (Int × Int) := (bt.getD j []).getD k none

/-- The bounds of the place numbered `n` of `L` in lane `k`, else those of any quadword. -/
def bndAt (bt : BT) (n : Option Nat) (k : Nat) : Int × Int :=
  match n with
  | some n => (bt.get (n / 5) k).getD (-2 ^ 63, 2 ^ 63 - 1)
  | none => (-2 ^ 63, 2 ^ 63 - 1)

/-- The number of the first place of `L` that is `l`. -/
def locIdx (L : List Loc) (l : Loc) : Option Nat :=
  let n := L.idxOf l
  if n < L.length then some n else none

/-- The slot at an offset of the working space, if it is one. -/
def slotAt (d : Nat) : Option Nat :=
  if cfg.sbase ≤ d ∧ (d - cfg.sbase) % 32 = 0 then some ((d - cfg.sbase) / 32) else none

/-- The bounds of what a piece starts from, by the places `L` and their bounds `bt`. -/
def bndsOf (L : List Loc) (bt : BT) : Bnds where
  vl r k := (bndAt bt (locIdx L (.reg r)) k).1
  vh r k := (bndAt bt (locIdx L (.reg r)) k).2
  ml b d k := if uBase b then 0
    else (bndAt bt (if b = .rdi then (slotAt d).bind fun i => locIdx L (.slot i) else none) k).1
  mh b d k := if uBase b then 2 ^ 64 - 1
    else (bndAt bt (if b = .rdi then (slotAt d).bind fun i => locIdx L (.slot i) else none) k).2

theorem toInt_range (x : BitVec 64) : -2 ^ 63 ≤ x.toInt ∧ x.toInt ≤ 2 ^ 63 - 1 := by
  have := x.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega_arith

theorem group5_getD : ∀ (ts : List T) (j i : Nat), i < 5 → 5 * j + 5 ≤ ts.length →
    ((group5 ts).getD j zero5).get i = ts.getD (5 * j + i) (.lit 0 0 0 0)
  | a :: b :: c :: d :: e :: rest, 0, i, hi, _ => by
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  | a :: b :: c :: d :: e :: rest, j + 1, i, hi, h => by
    have := group5_getD rest j i hi (by simp only [List.length_cons] at h; omega_using [h])
    simp only [group5, List.getD_cons_succ]
    rw [this, show 5 * (j + 1) + i = (5 * j + i) + 5 by omega_using []]
    rfl
  | [], _, _, _, h => by simp at h
  | [_], _, _, _, h => by simp at h
  | [_, _], _, _, _, h => by simp at h
  | [_, _, _], _, _, _, h => by simp at h
  | [_, _, _, _], _, _, _, h => by simp at h

/-- A limb of the vectors in the places `L` is the quadword of its place. -/
theorem tab_leaves (s : State) (L : List Loc) {j i : Nat} (hi : i < 5) (hj : 5 * j + 5 ≤ L.length) (k : Nat) :
    tab (envOf s) (leaves L) j i k = ints s (L.getD (5 * j + i) (.reg 0)) k := by
  have hl : 5 * j + i < L.length := by omega_using [hi, hj]
  rw [tab, leaves, group5_getD _ j i hi (by rw [List.length_map]; exact hj)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp only [Option.map_some, Option.getD_some]
  cases L[5 * j + i] <;> rfl

/-- What a piece starts from is within the bounds of its places. -/
theorem envOK_of {s : State} {L : List Loc} {bt : BT}
    (h : ∀ n l, L[n]? = some l → ∀ k, k < 4 → ∀ b, bt.get (n / 5) k = some b → b.1 ≤ ints s l k ∧ ints s l k ≤ b.2) :
    EnvOK s (bndsOf L bt) := by
  have key (l : Loc) (k : Nat) (hk : k < 4) :
      (bndAt bt (locIdx L l) k).1 ≤ ints s l k ∧ ints s l k ≤ (bndAt bt (locIdx L l) k).2 := by
    unfold locIdx bndAt
    dsimp only
    split
    · rename_i n hn
      split at hn
      · rename_i hlt
        cases hn
        have hl : L[L.idxOf l]? = some l := by
          rw [List.getElem?_eq_getElem hlt]; exact congrArg some (List.getElem_idxOf hlt)
        cases hb : bt.get (L.idxOf l / 5) k with
        | none => exact toInt_range _
        | some b => exact h _ l hl k hk b hb
      · cases hn
    · exact toInt_range _
  refine ⟨fun r k hk => key (.reg r) k hk, fun b d k hk => ?_⟩
  simp only [bndsOf]
  by_cases hu : uBase b = true
  · simp only [hu, ite_true, envOf]
    have := (s.mem.readW (s.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).isLt
    omega_using []
  have hm : (envOf s).m b d k = (s.mem.readW (s.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).toInt := by
    simp only [envOf, hu, Bool.false_eq_true, ite_false]
  simp only [hu, Bool.false_eq_true, ite_false]
  by_cases hb : b = .rdi
  · subst hb
    simp only [ite_true]
    cases hs : slotAt d with
    | none => rw [hm]; exact toInt_range _
    | some i =>
      simp only [Option.bind_some]
      have hd : d = slotOff i := by
        unfold slotAt at hs
        split at hs
        · rename_i hc; cases hs; simp only [slotOff]; omega_using [hc]
        · cases hs
      subst hd
      exact key (.slot i) k hk
  · simp only [hb, ite_false]
    rw [hm]
    exact toInt_range _

/-- The terms of the limbs of the lanes with bounds in `bt` have bounds within 64 signed bits. -/
def ivWithin (B : Bnds) (ts : List T) (bt : BT) : Bool :=
  ts.zipIdx.all fun (t, n) => (List.range 4).all fun k =>
    match bt.get (n / 5) k with
    | none => true
    | some b => match t.iv B k with
      | some iv => decide (b.1 ≤ iv.1 ∧ iv.2 ≤ b.2 ∧ -2 ^ 63 ≤ b.1 ∧ b.2 < 2 ^ 63)
      | none => false

/-- What a piece does, for integers: in the lanes with bounds in `bt`, the
limbs in the places of its results are those of the stage's terms, within
those bounds. -/
theorem stage_tab {w : Nat} {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSegW w c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B) {bt : BT}
    (hiv : ivWithin B (segT seg ins) bt = true) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, w)] s₀.mem s.mem ∧
      ∀ (n : Nat) (l : Loc) (t : T), outs[n]? = some l → (segT seg ins)[n]? = some t →
        ∀ k, k < 4 → ∀ b, bt.get (n / 5) k = some b →
          ints s l k = t.int (envOf s₀) k ∧ b.1 ≤ ints s l k ∧ ints s l k ≤ b.2 := by
  refine WP.mono (stage_int h hc hB) fun s ⟨hσ, hu, hs⟩ => ⟨hσ, hu, fun n l t hl ht k hk b hb => ?_⟩
  have hm : (t, n) ∈ (segT seg ins).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using ht
  have h1 := List.all_eq_true.1 hiv (t, n) hm
  have h2 := List.all_eq_true.1 h1 k (List.mem_range.2 hk)
  simp only [hb] at h2
  cases hiv' : t.iv B k with
  | none => simp [hiv'] at h2
  | some iv =>
    simp only [hiv', decide_eq_true_eq] at h2
    obtain ⟨e, lo, hi⟩ := hs n l t hl ht k hk iv hiv' (by omega_using [h2]) (by omega_using [h2])
    exact ⟨e, by omega_using [h2, e, lo], by omega_using [h2, e, hi]⟩

end

/-!
## What the blocks start from

The terms each block starts from: the accumulator in `ymm0`–`ymm19`, an
entry's vectors and the mask of its sign in memory.
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- The registers from `r` as a field vector. -/
def t5 (r : Nat) : F5 T := ⟨.reg r, .reg (r + 1), .reg (r + 2), .reg (r + 3), .reg (r + 4)⟩

/-- Five times 32 bytes from `b + d`, `n` bytes apart. -/
def ld5 (b : Reg) (d n : Nat) : F5 T := ⟨.ld b d, .ld b (d + n), .ld b (d + 2 * n), .ld b (d + 3 * n), .ld b (d + 4 * n)⟩

/-- The accumulator in `ymm0`–`ymm19`. -/
def stT : List (F5 T) := [t5 0, t5 5, t5 10, t5 15]

/-- The mask of an entry's sign. -/
def sgnT : F5 T := F5.rep (.ld .r9 0)

/-- What the addition starts from: the accumulator, the entry's two vectors and its sign. -/
def addT : List (F5 T) := stT ++ [t5 20, t5 25, sgnT]

def setT : List (F5 T) := [t5 20, sgnT]

/-- The words of a Jacobian point at `rcx` and of its `Z²` and `Z³` at `rdx`. -/
def rawQT : F5 T := ⟨.ld .rcx 0, .ld .rcx 32, .ld .rcx 64, .ld .rdx 0, .ld .rdx 32⟩

/-- The words of an affine point at `rdx`. -/
def rawGT : F5 T := ⟨.ld .rdx 0, .ld .rdx 32, .ld .rdx 0, .ld .rdx 0, .ld .rdx 0⟩

/-- What the entry of a Jacobian point starts from: the accumulator, and the point's words. -/
def convQT : List (F5 T) := stT ++ [rawQT]

def convGT : List (F5 T) := stT ++ [rawGT]

def regs20 : List Loc := (List.range 20).map .reg

def regs5 : List Loc := (List.range 5).map .reg

/-- The accumulator's registers and the entry's, `ymm20`–`ymm29`. -/
def regs30 : List Loc := (List.range 30).map .reg

/-- The words of an affine point: `x` at `rcx` and `y` at `rdx`. -/
def rawPT : F5 T := ⟨.ld .rcx 0, .ld .rdx 0, .ld .rcx 0, .ld .rcx 0, .ld .rcx 0⟩

/-- What the blocks of `Q`'s table start from: an entry in `ymm0`–`ymm9` and the points in `ymm10`–`ymm19`. -/
def tabT : List (F5 T) := [t5 0, t5 5, t5 10, t5 15]

/-- `ymm0`–`ymm9`. -/
def regs10 : List Loc := (List.range 10).map .reg

/-- The registers of the entry's first vector, `ymm20`–`ymm24`. -/
def regsE : List Loc := (List.range 5).map fun i => .reg (20 + i)

end

/-!
## The bounds a block starts from

The limbs of the accumulator in `ymm0`–`ymm19` (`stBT`: `u` in
`[-2⁶⁰ - 2⁵⁸, 2⁶⁰]`, `zn` and `n3` carried, `q3` in `[0, 2⁵⁶)`, each in its lanes),
and of an entry and the mask of its sign in memory (`entB`).
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- The bounds of carried limbs. -/
def carriedB : Option (Int × Int) := some (0, 2 ^ 52 - 1)

/-- The bounds of the accumulator's limbs: `u`, `zn`, `n3`, `q3`. -/
def stBT : BT :=
  [[some (-(2 ^ 60 + 2 ^ 58), 2 ^ 60), none, none, none],
   [none, carriedB, none, none],
   [none, carriedB, none, carriedB],
   [none, some (0, 2 ^ 56 - 1), none, some (0, 2 ^ 56 - 1)]]

/-- `B`, with the mask of an entry's sign at `r9` (zero, or all ones in the lanes 0 and 1). -/
def sgnB (B : Bnds) : Bnds where
  vl := B.vl
  vh := B.vh
  ml b d k := if b = .r9 ∧ d = 0 then (if k < 2 then -1 else 0) else B.ml b d k
  mh b d k := if b = .r9 ∧ d = 0 then 0 else B.mh b d k

/-- The bounds of an entry's limbs: `ta`, carried, and the first lane of `tb`. -/
def entBT : BT := [[carriedB, carriedB, carriedB, carriedB], [carriedB, none, none, none]]

/-- The bounds of the limbs of the points between the blocks of `Q`'s table, which are not carried. -/
def rawB : Option (Int × Int) := some (-2 ^ 60, 2 ^ 60)

/-- The bounds between the blocks of `Q`'s table: an entry, and the points `r` and `c`. -/
def tabBT : BT := entBT ++ [[rawB, rawB, rawB, none], [none, none, carriedB, carriedB]]

/-- The bounds the doubling and the conversion out start from. -/
def stB : Bnds := bndsOf regs20 stBT

/-- The bounds the addition starts from. -/
def addB : Bnds := sgnB (bndsOf regs30 (stBT ++ entBT))

/-- The bounds the first point starts from: the addition's. -/
def setB : Bnds := addB

/-- The terms of stage `j` of a block. -/
def stageT (locs : List (List Loc)) (segs : List (Seg Id T)) (ins : List (F5 T)) (j : Nat) : List T :=
  segT (segs.getD j (fun _ => pure [])) (if j = 0 then ins else leaves (locs.getD (j - 1) []))

/-- The bounds stage `j` of a block starts from: `B0`, or those of the places before it. -/
def stageB (locs : List (List Loc)) (bts : List BT) (B0 : Bnds) (j : Nat) : Bnds :=
  if j = 0 then B0 else bndsOf (locs.getD (j - 1) []) (bts.getD (j - 1) [])

end

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

def dblIV0 : BT :=
  [[some (-1337001217, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (-799081217, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblBT0 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblIV1 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblBT1 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblIV2 : BT :=
  [[some (-1, 2 ^ 52 - 1), some (-16252945, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblBT2 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblIV3 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblBT3 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblIV4 : BT :=
  [[some (-1686111829, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1686111829, 2 ^ 52 - 1), some (-50331697, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def dblBT4 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def dblIV5 : BT :=
  [[some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def dblBT5 : BT :=
  [[some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

/-- The bounds after each stage. -/
def dblBTs : List BT := [dblBT0, dblBT1, dblBT2, dblBT3, dblBT4, dblBT5]

/-- The bounds of the terms of each stage. -/
def dblIVs : List BT := [dblIV0, dblIV1, dblIV2, dblIV3, dblIV4, dblIV5]

def addIV0 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-1, 0), some (-1, 0), some (0, 0), some (0, 0)]]

def addBT0 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-1, 0), some (-1, 0), some (0, 0), some (0, 0)]]

def addIV1 : BT :=
  [[some (-334299457, 2 ^ 52 - 1), some (-12517389, 2 ^ 52 - 1), some (-12517389, 2 ^ 52 - 1), some (-12713997, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def addBT1 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def addIV2 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def addBT2 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def addIV3 : BT :=
  [[some (-12582925, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addBT3 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addIV4 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addBT4 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addIV5 : BT :=
  [[some (-12582925, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-150995089, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addBT5 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addIV6 : BT :=
  [[some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def addBT6 : BT :=
  [[some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

/-- The bounds after each stage. -/
def addBTs : List BT := [addBT0, addBT1, addBT2, addBT3, addBT4, addBT5, addBT6]

/-- The bounds of the terms of each stage. -/
def addIVs : List BT := [addIV0, addIV1, addIV2, addIV3, addIV4, addIV5, addIV6]

def setIV0 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)]]

def setBT0 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def setIV1 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def setBT1 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

/-- The bounds after each stage. -/
def setBTs : List BT := [setBT0, setBT1]

/-- The bounds of the terms of each stage. -/
def setIVs : List BT := [setIV0, setIV1]

def outIV0 : BT :=
  [[some (-334299457, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), none, some (-1, 2 ^ 52 - 1)]]

def outBT0 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), none, some (0, 2 ^ 52 - 1)]]

def outIV1 : BT :=
  [[some (0, 45264488534048764), some (0, 45299810344959994), some (0, 31824333273759742), some (0, 45264488534048764)]]

def outBT1 : BT :=
  [[some (0, 45264488534048764), some (0, 45299810344959994), some (0, 31824333273759742), some (0, 45264488534048764)]]

def outIV2 : BT :=
  [[some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)]]

def outBT2 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

/-- The bounds after each stage. -/
def outBTs : List BT := [outBT0, outBT1, outBT2]

/-- The bounds of the terms of each stage. -/
def outIVs : List BT := [outIV0, outIV1, outIV2]

def convQIV0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def convQBT0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

/-- The bounds after each stage. -/
def convQBTs : List BT := [convQBT0]

/-- The bounds of the terms of each stage. -/
def convQIVs : List BT := [convQIV0]

def convGIV0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (4, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (8, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (2, 2 ^ 52 - 1), some (0, 0), some (0, 0), some (0, 0)]]

def convGBT0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (4, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (8, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (2, 2 ^ 52 - 1), some (0, 0), some (0, 0), some (0, 0)]]

/-- The bounds after each stage. -/
def convGBTs : List BT := [convGBT0]

/-- The bounds of the terms of each stage. -/
def convGIVs : List BT := [convGIV0]

def tabGIV0 : BT :=
  [[some (4, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (8, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (2, 2 ^ 52 - 1), some (0, 0), some (0, 0), some (0, 0)]]

def tabGBT0 : BT :=
  [[some (4, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (8, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (2, 2 ^ 52 - 1), some (0, 0), some (0, 0), some (0, 0)]]

/-- The bounds after each stage. -/
def tabGBTs : List BT := [tabGBT0]

/-- The bounds of the terms of each stage. -/
def tabGIVs : List BT := [tabGIV0]

def dbluIV0 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluBT0 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluIV1 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-70713417, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluBT1 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluIV2 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluBT2 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluIV3 : BT :=
  [[some (-7471117, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-7471117, 2 ^ 52 - 1), some (-6422541, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluBT3 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-7471117, 2 ^ 52 - 1), some (-6422541, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def dbluIV4 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-434738651284897728, 76860329542221816), some (-217369325642448864, 58845931037982632), some (0, 239887323774058464), some (-434738651284897728, 81363929168543736)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def dbluBT4 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-434738651284897728, 76860329542221816), some (-217369325642448864, 58845931037982632), some (0, 239887323774058464), some (-434738651284897728, 81363929168543736)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

/-- The bounds after each stage. -/
def dbluBTs : List BT := [dbluBT0, dbluBT1, dbluBT2, dbluBT3, dbluBT4]

/-- The bounds of the terms of each stage. -/
def dbluIVs : List BT := [dbluIV0, dbluIV1, dbluIV2, dbluIV3, dbluIV4]

def zadduIV0 : BT :=
  [[some (-264306946, 2 ^ 52 - 1), some (-531694081, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-262209793, 2 ^ 52 - 1)],
   [some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT0 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduIV1 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT1 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-1152921504606846976, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduIV2 : BT :=
  [[some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-268435713, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT2 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduIV3 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT3 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduIV4 : BT :=
  [[some (-7471117, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-19071001, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT4 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduIV5 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT5 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduIV6 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-19071001, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-19071001, 2 ^ 52 - 1)],
   [some (0, 76860329542221816), some (0, 76860329542221816), some (-54342331410612216, 76860329542221816), some (0, 81363929168543736)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def zadduBT6 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-19071001, 2 ^ 52 - 1)],
   [some (0, 76860329542221816), some (0, 76860329542221816), some (-54342331410612216, 76860329542221816), some (0, 81363929168543736)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

/-- The bounds after each stage. -/
def zadduBTs : List BT := [zadduBT0, zadduBT1, zadduBT2, zadduBT3, zadduBT4, zadduBT5, zadduBT6]

/-- The bounds of the terms of each stage. -/
def zadduIVs : List BT := [zadduIV0, zadduIV1, zadduIV2, zadduIV3, zadduIV4, zadduIV5, zadduIV6]

end

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Weierstrass (Unch)

theorem group5_flat : ∀ xs : List (F5 T), group5 (xs.flatMap F5.toList) = xs
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, F5.toList, List.cons_append, List.nil_append, group5]
    rw [group5_flat xs]

theorem flat_length (xs : List (F5 T)) : (xs.flatMap F5.toList).length = 5 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, ih, F5.toList, List.length_cons, List.length_nil]; omega_using []

/-- A limb of the flattened vectors. -/
theorem flat_get (xs : List (F5 T)) {j i : Nat} (hi : i < 5) (hj : j < xs.length) :
    (xs.flatMap F5.toList)[5 * j + i]? = some ((xs.getD j zero5).get i) := by
  have h := group5_getD (xs.flatMap F5.toList) j i hi (by rw [flat_length]; omega_using [hj])
  rw [group5_flat] at h
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [flat_length]; omega_using [hi, hj])]
  rfl

theorem vI_get (E : Env) (k : Nat) (v : F5 T) :
    vI E k v = val5 ((v.get 0).int E k) ((v.get 1).int E k) ((v.get 2).int E k) ((v.get 3).int E k) ((v.get 4).int E k) :=
  rfl

/-- The bounds after a stage are those of its terms (or wider), but for the lanes `ovs`, which are carried. -/
def ovOk (bt iv : BT) (ovs : List (Nat × Nat)) : Bool :=
  (List.range bt.length).all fun j => (List.range ((bt.getD j []).length)).all fun k =>
    match bt.get j k with
    | none => true
    | some b => (match iv.get j k with
        | some c => decide (b.1 ≤ c.1 ∧ c.2 ≤ b.2)
        | none => false) ||
        (ovs.contains (j, k) && decide (b = (0, 2 ^ 52 - 1)) && (iv.get j k).isSome)

theorem ovOk_spec {bt iv : BT} {ovs : List (Nat × Nat)} (h : ovOk bt iv ovs = true) {j k : Nat} {b : Int × Int}
    (hb : bt.get j k = some b) :
    (∃ c, iv.get j k = some c ∧ b.1 ≤ c.1 ∧ c.2 ≤ b.2) ∨
      ((j, k) ∈ ovs ∧ b = (0, 2 ^ 52 - 1) ∧ ∃ c, iv.get j k = some c) := by
  have hj : j < bt.length := by
    by_contra hn
    simp only [BT.get, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn), Option.getD_none,
      List.getElem?_nil] at hb
    cases hb
  have hk : k < (bt.getD j []).length := by
    by_contra hn
    simp only [BT.get] at hb
    rw [List.getD_eq_getElem?_getD (l := bt.getD j []), List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hb
    cases hb
  have := List.all_eq_true.1 (List.all_eq_true.1 h j (List.mem_range.2 hj)) k (List.mem_range.2 hk)
  simp only [hb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
  rcases this with h1 | ⟨⟨h1, h2⟩, h3⟩
  · cases hc : iv.get j k with
    | none => simp [hc] at h1
    | some c =>
      simp only [hc, decide_eq_true_eq] at h1
      exact Or.inl ⟨c, rfl, h1⟩
  · exact Or.inr ⟨h1, h2, Option.isSome_iff_exists.1 h3⟩

theorem ivWithin_get {B : Bnds} {ts : List T} {bt : BT} (h : ivWithin B ts bt = true) {n k : Nat} {t : T}
    (ht : ts[n]? = some t) (hk : k < 4) {b : Int × Int} (hb : bt.get (n / 5) k = some b) :
    ∃ iv, t.iv B k = some iv ∧ b.1 ≤ iv.1 ∧ iv.2 ≤ b.2 ∧ -2 ^ 63 ≤ b.1 ∧ b.2 < 2 ^ 63 := by
  have hm : (t, n) ∈ ts.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using ht
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 h (t, n) hm) k (List.mem_range.2 hk)
  simp only [hb] at h2
  cases hiv : t.iv B k with
  | none => simp [hiv] at h2
  | some iv =>
    simp only [hiv, decide_eq_true_eq] at h2
    exact ⟨iv, rfl, h2⟩

theorem Carried.get {E : Env} {k : Nat} {v : F5 T} (h : Carried E k v) {i : Nat} (hi : i < 5) :
    0 ≤ (v.get i).int E k ∧ (v.get i).int E k < 2 ^ 52 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- The limbs of the vectors `ys` under `E'` are those of `xs` under `E`, in the lanes with bounds in `iv`. -/
def Same (iv : BT) (E' : Env) (ys : List (F5 T)) (E : Env) (xs : List (F5 T)) : Prop :=
  ∀ j k b, k < 4 → iv.get j k = some b → ∀ i, i < 5 → tab E' ys j i k = tab E xs j i k

theorem Same.vI {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) {j k : Nat} {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) : vI E' k (ys.getD j zero5) = vI E k (xs.getD j zero5) := by
  have e := h j k b hk hb
  simp only [tab] at e
  rw [vI_get, vI_get, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)]

theorem Same.carried {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) {j k : Nat}
    {b : Int × Int} (hk : k < 4) (hb : iv.get j k = some b) (hc : Carried E k (xs.getD j zero5)) :
    Carried E' k (ys.getD j zero5) := by
  have e := h j k b hk hb
  simp only [tab] at e
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide)
  simp only [F5.get] at e0 e1 e2 e3 e4
  unfold Carried at hc ⊢
  rw [e0, e1, e2, e3, e4]
  exact hc

theorem BT.get_lt {bt : BT} {j k : Nat} {b : Int × Int} (h : bt.get j k = some b) : j < bt.length := by
  by_contra hn
  simp only [BT.get, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn), Option.getD_none,
    List.getElem?_nil] at h
  cases h

/-- What a stage's piece of code does to what is known between the stages. -/
theorem cut_step {w : Nat} {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSegW w c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B)
    {iv bt : BT} {ovs : List (Nat × Nat)} (hiv : ivWithin B (segT seg ins) iv = true) (hov : ovOk bt iv ovs = true)
    (hlen : outs.length = 5 * (Id.run (seg ins)).length) (hrows : iv.length ≤ (Id.run (seg ins)).length)
    (hcar : ∀ j k, (j, k) ∈ ovs → Carried (envOf s₀) k ((Id.run (seg ins)).getD j zero5)) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, w)] s₀.mem s.mem ∧
        EnvOK s (bndsOf outs bt) ∧ Same iv (envOf s) (leaves outs) (envOf s₀) (Id.run (seg ins)) := by
  refine WP.mono (stage_tab h hc hB hiv) fun s ⟨hσ, hu, hs⟩ => ⟨hσ, hu, ?_, ?_⟩
  · refine envOK_of fun n l hl k hk b hb => ?_
    have hn : n < outs.length := (List.getElem?_eq_some_iff.1 hl).1
    have hj : n / 5 < (Id.run (seg ins)).length := by omega_using [hlen, hn]
    have ht := flat_get (Id.run (seg ins)) (i := n % 5) (Nat.mod_lt _ (by decide)) hj
    rw [show 5 * (n / 5) + n % 5 = n by omega_using []] at ht
    rcases ovOk_spec hov hb with ⟨c', h1, l1, l2⟩ | ⟨h1, h2, c', h3⟩
    · have := (hs n l _ hl ht k hk c' h1).2
      exact ⟨by omega_using [l1, this], by omega_using [l2, this]⟩
    · obtain ⟨e, -, -⟩ := hs n l _ hl ht k hk c' h3
      have := (hcar _ _ h1).get (i := n % 5) (Nat.mod_lt _ (by decide))
      rw [e, h2]
      exact ⟨this.1, by have := this.2; omega_arith⟩
  · intro j k b hk hb i hi
    have hj : j < (Id.run (seg ins)).length := Nat.lt_of_lt_of_le (BT.get_lt hb) hrows
    have ht := flat_get (Id.run (seg ins)) hi hj
    have hn : 5 * j + i < outs.length := by omega_using [hlen, hi, hj]
    have hl : outs[5 * j + i]? = some (outs.getD (5 * j + i) (.reg 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
    rw [tab_leaves s outs hi (by omega_using [hlen, hj]) k]
    exact (hs (5 * j + i) _ _ hl ht k hk b (by rw [show (5 * j + i) / 5 = j by omega_using [hi]]; exact hb)).1

theorem par_cst_length : par.cst.length = 220 := by decide +kernel

/-- A piece of code leaves what the next may read and write, and the constants. -/
theorem ctx_step {σ : VSym} {s₀ s : State} (hc : Ctx par s₀) (h : SRel par σ s₀ s) : Ctx par s := by
  have hg := h.gpr
  refine ⟨?_, hc.small, ?_, ?_, ?_, ?_, ?_, hc.cb⟩
  · intro d hd; rw [h.wr, hg]; exact hc.win d hd
  · intro b d hb hcb hd; rw [h.rd, h.wr, hg]; exact hc.rd b d hb hcb hd
  · intro b d hb hcb hd; rw [hg]; exact hc.sep b d hb hcb hd
  · intro d hd; rw [h.rd, h.wr, hg]; exact hc.crd d hd
  · intro d hd; rw [hg]; exact hc.csep d hd
  · intro i hi
    rw [par_cst_length] at hi
    -- the 32 bytes of the constants that hold quadword `i`
    have hd : 8 * (min i 216) + 32 ≤ 8 * par.cst.length := by rw [par_cst_length]; omega_using []
    have e := stores_sep (hc.csep _ hd) hc.small (k := i - min i 216) (by omega_using [hi]) σ.st h.al h.lo
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * min i 216 + 8 * (i - min i 216) = 8 * i by omega_using []] at e
    rw [h.mem, hg, e]
    exact hc.cst i (by rw [par_cst_length]; exact hi)

end VG.Proof.P256.X86_64.Ifma
