module

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Code
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Sym

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
  split <;> omega

theorem R64.toNat (x : BitVec 64) : R64 x (x.toNat : Int) := by
  have := x.isLt
  rw [R64]; omega

theorem R64.ofNat (w : Nat) : R64 (BitVec.ofNat 64 w) (w : Int) := by
  rw [R64, BitVec.toNat_ofNat]; omega

theorem R64.add {x y : BitVec 64} {X Y : Int} (hx : R64 x X) (hy : R64 y Y) : R64 (x + y) (X + Y) := by
  rw [R64] at *; rw [BitVec.toNat_add]; omega

theorem R64.sub {x y : BitVec 64} {X Y : Int} (hx : R64 x X) (hy : R64 y Y) : R64 (x - y) (X - Y) := by
  have := y.isLt
  rw [R64] at *; rw [BitVec.toNat_sub]; omega

/-- A number in `[0, 2⁶⁴)` is its quadword's. -/
theorem R64.nat {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : 0 ≤ X) (h1 : X < 2 ^ 64) : (x.toNat : Int) = X := by
  rw [R64] at hx; omega

/-- A number in `[-2⁶³, 2⁶³)` is its quadword's, signed. -/
theorem R64.int {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : -2 ^ 63 ≤ X) (h1 : X < 2 ^ 63) : x.toInt = X := by
  have := x.isLt
  rw [R64] at hx
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem emod_mul_pow (X : Int) (q : Int) : (X % 2 ^ 64 * q) % 2 ^ 64 = (X * q) % 2 ^ 64 := by
  have e : X * q = X % 2 ^ 64 * q + 2 ^ 64 * (X / 2 ^ 64 * q) := by
    have : X = X % 2 ^ 64 + 2 ^ 64 * (X / 2 ^ 64) := by omega
    grind
  rw [e, Int.add_mul_emod_self_left]

theorem R64.shl {x : BitVec 64} {X : Int} (hx : R64 x X) (n : Nat) : R64 (x <<< n) (X * 2 ^ n) := by
  rw [R64] at *
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx, ← emod_mul_pow]
  have h0 : 0 ≤ X % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
  rw [hN, Int.toNat_natCast, show ((N : Int) * 2 ^ n) = ((N * 2 ^ n : Nat) : Int) by push_cast; rfl]
  omega

theorem R64.shr {x : BitVec 64} {X : Int} (hx : R64 x X) (h0 : 0 ≤ X) (h1 : X < 2 ^ 64) (n : Nat) :
    R64 (x >>> n) (X / 2 ^ n) := by
  have e := hx.nat h0 h1
  rw [R64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← e,
    show ((x.toNat : Int) / 2 ^ n) = ((x.toNat / 2 ^ n : Nat) : Int) by push_cast; rfl]
  have := Nat.div_le_self x.toNat (2 ^ n)
  have := x.isLt
  generalize x.toNat / 2 ^ n = K at *
  omega

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
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod]
  rw [R64] at *
  rw [e]
  split
  · rename_i h64
    have : j = 64 := by omega
    subst this
    have := x.isLt
    omega
  · have h0 : 0 ≤ X % 2 ^ 64 := Int.emod_nonneg _ (by decide)
    obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
    have d : ((2 : Int) ^ j) ∣ 2 ^ 64 := ⟨2 ^ (64 - j), by rw [← Int.pow_add]; congr 1; omega⟩
    have e2 : X % 2 ^ j = ((N % 2 ^ j : Nat) : Int) := by
      rw [← Int.emod_emod_of_dvd X d, hN]; push_cast; rfl
    rw [hx, hN, Int.toNat_natCast, e2]
    have := Nat.mod_lt N hp0
    omega

theorem R64.mad {c a b : BitVec 64} {C A B : Int} (hc : R64 c C) (ha : R64 a A) (hb : R64 b B) (h : Bool) :
    R64 (mad52 h c a b) (C + (if h then A % 2 ^ 52 * (B % 2 ^ 52) / 2 ^ 52 else A % 2 ^ 52 * (B % 2 ^ 52) % 2 ^ 52)) := by
  have a0 : 0 ≤ A % 2 ^ 52 := Int.emod_nonneg _ (by decide)
  have b0 : 0 ≤ B % 2 ^ 52 := Int.emod_nonneg _ (by decide)
  obtain ⟨M, hM⟩ := Int.eq_ofNat_of_zero_le a0
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le b0
  have ea : a.toNat % 2 ^ 52 = M := by rw [R64] at ha; omega
  have eb : b.toNat % 2 ^ 52 = N := by rw [R64] at hb; omega
  rw [R64] at *
  rw [mad52_toNat, ea, eb, hM, hN, show ((M : Int) * (N : Int)) = ((M * N : Nat) : Int) by push_cast; rfl]
  generalize M * N = Q
  cases h <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

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
  · have hC1 : C = -1 := by omega
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
    rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact h2
  · have := Int.emod_lt_of_pos X (show (0 : Int) < 2 ^ 52 by decide)
    omega

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
    exact ⟨ra.shr (by omega) (by omega) n, Int.ediv_le_ediv (pow_pos' n) la, Int.ediv_le_ediv (pow_pos' n) ua⟩
  | sra a n iha =>
    intro k iv hk h
    simp only [T.iv, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    case isFalse => cases h
    rename_i hr
    cases h
    obtain ⟨ra, la, ua⟩ := iha k x hk hx
    exact ⟨ra.sra (by omega) (by omega) n, Int.ediv_le_ediv (pow_pos' n) la, Int.ediv_le_ediv (pow_pos' n) ua⟩
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
    refine ⟨ra.mask (by omega), ?_⟩
    split at h
    · rename_i h64
      cases h
      simp only [h64, ↓reduceIte]; exact ⟨la, ua⟩
    · rename_i h64
      simp only [h64, ↓reduceIte]
      split at h
      · rename_i hr
        cases h
        rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact ⟨la, ua⟩
      · cases h
        have := Int.emod_lt_of_pos (a.int (envOf s₀) k) (pow_pos' j)
        exact ⟨Int.emod_nonneg _ (Int.ne_of_gt (pow_pos' j)), by omega⟩
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
        simp only [T.int]; omega
      · have := Int.emod_lt_of_pos (a.int (envOf s₀) k % 2 ^ 52 * (b.int (envOf s₀) k % 2 ^ 52))
          (show (0 : Int) < 2 ^ 52 by decide)
        simp only [T.int]; omega
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
        simp only [T.int]; omega
      · have := Int.ediv_le_ediv (show (0 : Int) < 2 ^ 52 by decide) hp
        simp only [T.int]; omega
  | slr a n j iha =>
    intro k iv hk h
    simp only [T.iv, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨ra, -, -⟩ := iha k x hk hx
    have h0 : 0 ≤ a.int (envOf s₀) k * 2 ^ n % 2 ^ 64 := Int.emod_nonneg _ (by decide)
    have h1 : a.int (envOf s₀) k * 2 ^ n % 2 ^ 64 ≤ 2 ^ 64 - 1 := by
      have := Int.emod_lt_of_pos (a.int (envOf s₀) k * 2 ^ n) (show (0 : Int) < 2 ^ 64 by decide)
      omega
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
    refine ⟨rc.sel ra rb (by omega) (by omega), ?_⟩
    simp only [T.int]
    split <;> omega

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
are from `4512` of it. -/
def par : Par :=
  ⟨.r10, poolLit.flatMap fun k => [k.w0, k.w1, k.w2, k.w3],
    fun r => if r = .rcx then 96 else if r = .rdx then 64 else if r = .r9 then 32 else 0, 5408, 4512⟩

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

/-- The code of a stage computes its terms, into the places `outs`, and stores only into the slots. -/
def chkSeg (code : List Instr) (ins : List (F5 T)) (seg : Seg Id T) (outs : List Loc) : Bool :=
  match VSym.init.run par code with
  | some σ => decide (outs.map (termAt σ) = segT seg ins) && outs.all locOk &&
    σ.st.all fun e => decide (cfg.sbase ≤ e.1)
  | none => false

/-- Stage `j` of a block, from the terms `ins` at its start, its last stage's values into `fin`. -/
def chkStage (pieces : List (List Instr)) (locs : List (List Loc)) (segs : List (Seg Id T)) (ins : List (F5 T))
    (fin : List Loc) (j : Nat) : Bool :=
  let i := if j = 0 then ins else group5 ((locs.getD (j - 1) []).map leafOf)
  let o := if j + 1 = segs.length then fin else locs.getD j []
  chkSeg (pieces.getD j []) i (segs.getD j (fun _ => pure [])) o

theorem slotOff_mod (i : Nat) : slotOff i % 32 = 0 := by
  simp only [slotOff, cfg]; omega

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

/-- Stores from `lo` up change nothing below `lo` or from the working space's end. -/
theorem stores_unch (s₀ : State) (lo : Nat) :
    ∀ (st : List (Nat × T)), (∀ e ∈ st, (e.1 % 32 = 0 ∧ e.1 + 32 ≤ par.win) ∧ lo ≤ e.1) →
      Unch (s₀.gpr .rdi) [(lo, par.win - lo)] s₀.mem (stores s₀ st)
  | [], _ => Unch.refl _ _ _
  | (e, t) :: st, he => by
    have he0 := he (e, t) List.mem_cons_self
    intro x hx
    have h1 := hx (lo, par.win - lo) (List.mem_singleton.2 rfl)
    simp only [stores]
    rw [writeW_byte_off _ _ _ _ ?_]
    · exact stores_unch s₀ lo st (fun y hy => he y (List.mem_cons_of_mem _ hy)) x hx
    · simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.reduceDiv]
      have := (x - s₀.gpr .rdi).isLt
      have hw : par.win = 5408 := rfl
      simp only [VG.Proof.Mont.ofs] at h1
      omega

/-- What a piece does: every quadword of every place of its results is its
term, of the state before; nothing else of the state changes but vector
registers and the slots of the working space. -/
theorem stage_wp {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSeg c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, par.win - cfg.sbase)] s₀.mem s.mem ∧
      ∀ (j : Nat) (l : Loc) (t : T), outs[j]? = some l → (segT seg ins)[j]? = some t →
        ∀ k, k < 4 → lanesAt s l k = t.eval s₀ k := by
  unfold chkSeg at h
  split at h
  case h_2 => cases h
  rename_i σ hσ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine WP.mono (srun_ok hc c (SRel.init par s₀) hσ) fun s hs => ⟨⟨σ, hs⟩, ?_, fun j l t hl ht k hk => ?_⟩
  · rw [hs.mem]
    refine stores_unch s₀ cfg.sbase σ.st fun e he => ⟨hs.al e he, ?_⟩
    have := List.all_eq_true.1 h.2 e he
    simpa using this
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
theorem stage_int {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSeg c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, par.win - cfg.sbase)] s₀.mem s.mem ∧
      ∀ (j : Nat) (l : Loc) (t : T), outs[j]? = some l → (segT seg ins)[j]? = some t →
        ∀ k, k < 4 → ∀ iv, t.iv B k = some iv → -2 ^ 63 ≤ iv.1 → iv.2 < 2 ^ 63 →
          ints s l k = t.int (envOf s₀) k ∧ iv.1 ≤ t.int (envOf s₀) k ∧ t.int (envOf s₀) k ≤ iv.2 := by
  refine WP.mono (stage_wp h hc) fun s ⟨hσ, hu, hs⟩ => ⟨hσ, hu, fun j l t hl ht k hk iv hiv h0 h1 => ?_⟩
  obtain ⟨r, lo, hi⟩ := iv_ok hB t k iv hk hiv
  rw [ints, hs j l t hl ht k hk]
  exact ⟨r.int (by omega) (by omega), lo, hi⟩

end VG.Proof.P256.X86_64.Ifma
