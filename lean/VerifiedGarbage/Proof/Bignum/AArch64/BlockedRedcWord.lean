module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.Square
public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Bignum.AArch64.BlockedRedcMath`, which this module and modules that import it used -/

section

/-! Arithmetic invariants for a register block of Montgomery multiply-adds.
Low and high product halves use separate carry chains, as in the x86-64
register-blocked arithmetic, but the AArch64 implementation serializes them.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG.Proof.Bignum.Square

theorem value_congr {r n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    value r f n = value r g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, value, h n (by omega_using []), ih (fun i hi => h i (by omega_using [hi]))]


open VG.Proof.Ed25519.Word64

/-- Carry entering word `i` of an ordinary scalar carry chain. -/
def chainCarry (a b : Nat → Word) (c : Bool) : Nat → Bool
  | 0 => c
  | i + 1 => carryOut (a i) (b i) (chainCarry a b c i)

/-- Conservation of the entire chain, including both boundary carries. -/
theorem chain_value (a b : Nat → Word) (c : Bool) (n : Nat) :
    value (2 ^ 64) (fun i => (addCarry (a i) (b i) (chainCarry a b c i)).toNat) n +
      (2 ^ 64) ^ n * (chainCarry a b c n).toNat =
      value (2 ^ 64) (fun i => (a i).toNat) n +
        value (2 ^ 64) (fun i => (b i).toNat) n + c.toNat := by
  induction n with
  | zero => simp only [value, chainCarry, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | succ n ih =>
    have h := addCarry_value (a n) (b n) (chainCarry a b c n)
    simp only [value, chainCarry, Nat.pow_succ]
    grind


/-- Re-express a block after its low digit is emitted. -/
theorem value_shift (r : Nat) (f : Nat → Nat) (n : Nat) :
    f 0 + r * value r (fun i => f (i + 1)) n = value r f (n + 1) := by
  induction n with
  | zero => simp only [value, Nat.pow_zero, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    simp only [value, Nat.pow_succ]
    simp only [value] at ih
    grind

/-- A full block product plus two bounded accumulator blocks cannot overflow
its two-block result. This justifies discarding the high-chain flag after
all eight rows, without assuming that the Montgomery inverse is valid. -/
theorem tile_carry_zero {r a x q n lo hi c : Nat}
    (hr : 1 < r) (ha : a < r) (hx : x < r) (hq : q < r) (hn : n < r)
    (hv : lo + r * (hi + r * c) = a + x + q * n) : c = 0 := by
  have hq' : q ≤ r - 1 := by omega_using [hq]
  have hn' : n ≤ r - 1 := by omega_using [hn]
  have hp := Nat.mul_le_mul hq' hn'
  have he : r * r = (r - 1) * (r - 1) + 2 * (r - 1) + 1 := by
    have h : r = (r - 1) + 1 := by omega_using [hr]
    calc
      r * r = ((r - 1) + 1) * ((r - 1) + 1) := congrArg (fun v => v * v) h
      _ = (r - 1) * (r - 1) + 2 * (r - 1) + 1 := by grind
  have ht : a + x + q * n < r * r := by omega_using [ha, hx, hp, he]
  by_contra hc
  have hc' : 1 ≤ c := by omega
  have hm := Nat.mul_le_mul_left (r * r) hc'
  simp only [Nat.mul_one] at hm
  rw [Nat.mul_add, ← Nat.mul_assoc] at hv
  omega_using [hr, ha, hx, hq, hn, hv, hq', hn', hp, he, ht, hc', hm]


/-- Combine the two carry chains and the shift without losing either carry. -/
theorem chained_row_value {b r a q n low high aLow cLow shifted aHigh cHigh cin lo : Nat}
    (hlow : aLow + r * cLow = a + low)
    (hshift : lo + b * shifted = aLow + r * (cin + cLow))
    (hhigh : aHigh + r * cHigh = shifted + high)
    (hprod : low + b * high = q * n) :
    lo + b * (aHigh + r * cHigh) = a + q * n + r * cin := by
  grind

/-- A block of bounded digits is smaller than its radix power. -/
theorem value_lt (r : Nat) (f : Nat → Nat) (k : Nat)
    (hf : ∀ i < k, f i < r) : value r f k < r ^ k := by
  induction k with
  | zero => simp only [value, Nat.pow_zero]; omega_using []
  | succ k ih =>
    have hp := ih (fun i hi => hf i (by omega_using [hi]))
    have hd : f k + 1 ≤ r := by have := hf k (by omega_using []); omega_using [this]
    calc
      value r f (k + 1) = value r f k + f k * r ^ k := rfl
      _ < r ^ k + f k * r ^ k := Nat.add_lt_add_right hp _
      _ = (f k + 1) * r ^ k := by grind
      _ ≤ r * r ^ k := Nat.mul_le_mul_right _ hd
      _ = r ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- A cancellation row has no incoming carry. Its quotient fits the
register block even if the supplied Montgomery inverse is malformed. -/
theorem cancel_carry_zero {b r a q n lo hi c : Nat}
    (hb : 0 < b) (ha : a < r) (hq : q < b) (hn : n < r)
    (hv : lo + b * (hi + r * c) = a + q * n) : c = 0 := by
  have hq' : q + 1 ≤ b := by omega_using [hq]
  have hn' : n ≤ r - 1 := by omega_using [hn]
  have hp := Nat.mul_le_mul_left q hn'
  have hprod := Nat.mul_le_mul_right (r - 1) hq'
  have he : b * r = b * (r - 1) + b := by
    have hr : r = (r - 1) + 1 := by omega_using [ha]
    calc
      b * r = b * ((r - 1) + 1) := congrArg (b * ·) hr
      _ = b * (r - 1) + b := by rw [Nat.mul_add, Nat.mul_one]
  have ht : a + q * n < b * r := by
    rw [Nat.add_mul, Nat.one_mul] at hprod
    omega_using [hb, ha, hp, hprod, he]
  by_contra hc
  have hm := Nat.mul_le_mul_left (b * r) (show 1 ≤ c by omega)
  simp only [Nat.mul_one] at hm
  rw [Nat.mul_add, ← Nat.mul_assoc] at hv
  omega_using [hv, ht, hm]

/-- Extend the accumulated block equation by one emitted digit. -/
theorem rows_step {b p out state next initial qsum q n lo : Nat}
    (hp : out + p * state = initial + qsum * n)
    (hr : lo + b * next = state + q * n) :
    (out + p * lo) + (p * b) * next = initial + (qsum + p * q) * n := by
  have hs := congrArg (p * ·) hr
  grind

/-- Extend a canceled prefix while retaining its coefficients. -/
theorem cancel_step {b p state next initial qsum q n : Nat}
    (hp : p * state = initial + qsum * n)
    (hr : b * next = state + q * n) :
    (p * b) * next = initial + (qsum + p * q) * n := by
  have hs := congrArg (p * ·) hr
  grind

theorem zero_carry_value {r out acc c rhs : Nat} (hc : c = 0)
    (hv : out + r * (acc + r * c) = rhs) : out + r * acc = rhs := by
  subst c
  simpa only [Nat.mul_zero, Nat.add_zero] using hv

theorem columns_step {r p out acc next initial input modulus q lo x n : Nat}
    (hp : out + p * acc = initial + input + q * modulus)
    (hr : lo + r * next = acc + x + q * n) :
    (out + p * lo) + (p * r) * next =
      initial + (input + p * x) + q * (modulus + p * n) := by
  have hs := congrArg (p * ·) hr
  grind

theorem columns_initial (a q : Nat) : 0 + 1 * a = a + 0 + q * 0 := by
  simp only [Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero]

/-- Combine cancellation, the middle columns, and the pending-carry column
into one complete blocked Montgomery row. -/
theorem block_row_value {r p q a0 ac mid af last inputMid inputLast n0 nMid oldCarry carry : Nat}
    (hC : r * ac = a0 + q * n0)
    (hM : mid + p * af = ac + inputMid + q * nMid)
    (hF : last + r * carry = af + inputLast + oldCarry) :
    r * ((mid + p * last) + (r * p) * carry) =
      (a0 + r * (inputMid + p * inputLast)) + q * (n0 + r * nMid) +
        (r * p) * oldCarry := by
  have hm := congrArg (r * ·) hM
  have hf := congrArg ((r * p) * ·) hF
  grind

theorem row_extend {r w lo hi q n p p' tail : Nat}
    (h : r * (lo + w * p') = hi + q * n + w * p) :
    r * ((lo + w * tail) + w * p') = (hi + (w * r) * tail) + q * n + w * p := by
  grind

theorem append_digit_bound {r p q d : Nat} (hq : q < p) (hd : d < r) :
    q + p * d < p * r := by
  have hr : r = (r - 1) + 1 := by omega_using [hd]
  have hh := Nat.mul_le_mul_left p (show d ≤ r - 1 by omega_using [hd])
  have hp : p * r = p * (r - 1) + p :=
    (congrArg (p * ·) hr).trans (by rw [Nat.mul_add, Nat.mul_one])
  omega_using [hq, hh, hp]

theorem outer_initial {v raw w c n : Nat} (hv : v = raw) (hc : c = 0) :
    1 * (v + w * c) = raw + 0 * n := by
  rw [hv, hc]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.one_mul, Nat.zero_mul]

end VG.Proof.Bignum.AArch64.BlockedRedc

end

end

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The modulus block has seven words resident in registers and one in memory. -/
def operand (s : State) (n0 : Word) (i : Nat) : Word :=
  ([n0, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5,
    s.gpr .x6, s.gpr .x9, s.gpr .x11]).getD i 0

def accumulator (s : State) (i : Nat) : Word :=
  ([s.gpr .x19, s.gpr .x20, s.gpr .x21, s.gpr .x22,
    s.gpr .x23, s.gpr .x24, s.gpr .x25, s.gpr .x26]).getD i 0

def lowProduct (s : State) (n0 : Word) (i : Nat) : Word :=
  s.gpr .x27 * operand s n0 i

def highProduct (s : State) (n0 : Word) (i : Nat) : Word :=
  BitVec.ofNat 64 ((s.gpr .x27).toNat * (operand s n0 i).toNat / 2 ^ 64)

theorem lowChain_ok {s : State} {B : Addr} {Z eN : Nat}
    (hs : Scr s B Z) (h17 : s.gpr .x17 = off B eN) (hN : eN + 8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.lowChain) s fun t =>
      (t.c = chainCarry (accumulator s) (lowProduct s (word s.mem B eN)) false 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! = addCarry (accumulator s i)
         (lowProduct s (word s.mem B eN) i)
         (chainCarry (accumulator s) (lowProduct s (word s.mem B eN)) false i)) ∧
       (∀ i < 4, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.tt[i]! = highProduct s (word s.mem B eN) i) ∧
       t.mem = s.mem) ∧ Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt) s t := by
  refine WP.keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt) ?_ (by decide) (by decide) (by decide +kernel)
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  brun [↓RegUpd.gpr_write, ↓reduceIte, h4, h8, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, VG.Impl.Bignum.AArch64.BlockedRedc.lowChain, VG.Impl.Bignum.AArch64.BlockedRedc.product, VG.Impl.Bignum.AArch64.BlockedRedc.aa, VG.Impl.Bignum.AArch64.BlockedRedc.nn, VG.Impl.Bignum.AArch64.BlockedRedc.tt, h17, hs.ld hN]
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  · intro i hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    all_goals rfl


/-- The low chain shifts one word before the high product halves are added. -/
def shifted (s : State) (i : Nat) : Word :=
  ([s.gpr .x20, s.gpr .x21, s.gpr .x22, s.gpr .x23,
    s.gpr .x24, s.gpr .x25, s.gpr .x26, s.gpr .x1]).getD i 0

/-- Four high halves are already scheduled; the other four are computed
while the high carry chain runs. -/
def highTerms (s : State) (i : Nat) : Word :=
  ([s.gpr .x13, s.gpr .x14, s.gpr .x28, s.gpr .x30,
    highProduct s 0 4, highProduct s 0 5,
    highProduct s 0 6, highProduct s 0 7]).getD i 0

theorem highChain_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.highChain) s fun t =>
      (t.c = chainCarry (shifted s) (highTerms s) false 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
         addCarry (shifted s i) (highTerms s i)
           (chainCarry (shifted s) (highTerms s) false i)) ∧
       t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt) s t := by
  refine WP.keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
    VG.Impl.Bignum.AArch64.BlockedRedc.tt) ?_ (by decide) (by decide) (by decide +kernel)
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  brun [↓RegUpd.gpr_write, ↓reduceIte, h8, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    VG.Impl.Bignum.AArch64.BlockedRedc.highChain, VG.Impl.Bignum.AArch64.BlockedRedc.product,
    VG.Impl.Bignum.AArch64.BlockedRedc.aa, VG.Impl.Bignum.AArch64.BlockedRedc.nn,
    VG.Impl.Bignum.AArch64.BlockedRedc.tt]
  refine ⟨?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [shifted, highTerms, highProduct, operand, chainCarry, addCarry, VG.Proof.Ed25519.Word64.carryOut,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, List.getElem!_cons_zero, List.getElem!_cons_succ,
        off, BitVec.ofNat_add, BitVec.add_assoc, reduceCtorEq, ↓reduceIte,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod]


/-- The eight words currently held in accumulator registers. -/
def blockValue (f : Nat → Word) : Nat :=
  VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (f i).toNat) 8

theorem accumulator_reg (s : State) {i : Nat} (hi : i < 8) :
    accumulator s i = s.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem blockValue_congr {a b : Nat → Word} (h : ∀ i < 8, a i = b i) :
    blockValue a = blockValue b :=
  value_congr (fun i hi => congrArg BitVec.toNat (h i hi))

/-- The instruction-level carry-chain result implies full-block conservation. -/
theorem chain_result_value {t : State} {a b : Nat → Word} {c : Bool}
    (hc : t.c = chainCarry a b c 8)
    (hv : ∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
      addCarry (a i) (b i) (chainCarry a b c i)) :
    blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat =
      blockValue a + blockValue b + c.toNat := by
  have ha : blockValue (accumulator t) =
      blockValue (fun i => addCarry (a i) (b i) (chainCarry a b c i)) :=
    blockValue_congr (fun i hi => (accumulator_reg t hi).trans (hv i hi))
  rw [ha, hc]
  exact chain_value a b c 8

/-- The scheduled low and high halves retain the whole scalar/block product. -/
theorem block_product_value (s : State) (n0 : Word) :
    blockValue (lowProduct s n0) + 2 ^ 64 * blockValue (highProduct s n0) =
      (s.gpr .x27).toNat * blockValue (operand s n0) := by
  suffices h : ∀ n,
      VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (lowProduct s n0 i).toNat) n +
        2 ^ 64 * VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (highProduct s n0 i).toNat) n =
      (s.gpr .x27).toNat * VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (operand s n0 i).toNat) n by
    exact h 8
  intro n
  induction n with
  | zero => simp only [VG.Proof.Bignum.Square.value, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have h := mul_toNat (s.gpr .x27) (operand s n0 n)
    change (lowProduct s n0 n).toNat + 2 ^ 64 * (highProduct s n0 n).toNat =
      (s.gpr .x27).toNat * (operand s n0 n).toNat at h
    simp only [VG.Proof.Bignum.Square.value]
    grind


/-- Shifting the low-chain accumulator exposes its low word and appends the
captured high carry word. -/
theorem shifted_value (s : State) :
    (s.gpr .x19).toNat + 2 ^ 64 * blockValue (shifted s) =
      blockValue (accumulator s) + (2 ^ 64) ^ 8 * (s.gpr .x1).toNat := by
  have ht : VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (shifted s i).toNat) 7 =
      VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (accumulator s (i + 1)).toNat) 7 := by
    apply value_congr
    intro i hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  have hs := value_shift (2 ^ 64) (fun i => (accumulator s i).toNat) 7
  have hp : 2 ^ 64 * (2 ^ 64) ^ 7 = (2 ^ 64) ^ 8 := by
    rw [Nat.pow_succ (2 ^ 64) 7, Nat.mul_comm]
  unfold blockValue
  rw [VG.Proof.Bignum.Square.value]
  rw [show shifted s 7 = s.gpr .x1 from rfl, ht]
  rw [show accumulator s 0 = s.gpr .x19 from rfl] at hs
  rw [Nat.mul_add, ← Nat.add_assoc]
  rw [show 2 ^ 64 * ((s.gpr .x1).toNat * (2 ^ 64) ^ 7) =
    (2 ^ 64 * (2 ^ 64) ^ 7) * (s.gpr .x1).toNat by ac_rfl]
  simp only [Nat.reduceAdd] at hs
  rewrite [hp, hs]
  rfl


theorem accumulator_congr {s t : State}
    (h : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.aa, t.gpr r = s.gpr r) :
    accumulator t = accumulator s := by
  funext i
  simp only [accumulator, h .x19 (by decide), h .x20 (by decide), h .x21 (by decide),
    h .x22 (by decide), h .x23 (by decide), h .x24 (by decide), h .x25 (by decide), h .x26 (by decide)]

theorem highTerms_value {s t : State} (n0 : Word)
    (h13 : t.gpr .x13 = highProduct s n0 0) (h14 : t.gpr .x14 = highProduct s n0 1)
    (h28 : t.gpr .x28 = highProduct s n0 2) (h30 : t.gpr .x30 = highProduct s n0 3)
    (h27 : t.gpr .x27 = s.gpr .x27) (h5 : t.gpr .x5 = s.gpr .x5)
    (h6 : t.gpr .x6 = s.gpr .x6) (h9 : t.gpr .x9 = s.gpr .x9)
    (h11 : t.gpr .x11 = s.gpr .x11) :
    blockValue (highTerms t) = blockValue (highProduct s n0) := by
  apply blockValue_congr
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [highTerms, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, h13, h14, h28, h30,
      highProduct, operand, h27, h5, h6, h9, h11]


theorem keep_accumulator {s t : State} {rs : List Reg} (h : Keep rs s t)
    (hd : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.aa, r ∉ rs) :
    accumulator t = accumulator s := accumulator_congr (fun r hr => h.gpr r (hd r hr))

theorem keep_operand {s t : State} {rs : List Reg} (h : Keep rs s t)
    (hd : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.nn, r ∉ rs) (n0 : Word) :
    operand t n0 = operand s n0 := by
  funext i
  have h2 := h.gpr .x2 (hd .x2 (by decide))
  have h3 := h.gpr .x3 (hd .x3 (by decide))
  have h4 := h.gpr .x4 (hd .x4 (by decide))
  have h5 := h.gpr .x5 (hd .x5 (by decide))
  have h6 := h.gpr .x6 (hd .x6 (by decide))
  have h9 := h.gpr .x9 (hd .x9 (by decide))
  have h11 := h.gpr .x11 (hd .x11 (by decide))
  simp only [operand, h2, h3, h4, h5, h6, h9, h11]

theorem blockValue_lt (f : Nat → Word) : blockValue f < (2 ^ 64) ^ 8 :=
  value_lt _ _ _ (fun i _ => (f i).isLt)

theorem value_words (m : Mem) (B : Addr) (e k : Nat) :
    VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (word m B (e + 8 * i)).toNat) k =
      wv m B e k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change VG.Proof.Bignum.Square.value (2 ^ 64) (fun i => (word m B (e + 8 * i)).toNat) k +
      (word m B (e + 8 * k)).toNat * (2 ^ 64) ^ k =
      wv m B e k + 2 ^ (64 * k) * (word m B (e + 8 * k)).toNat
    exact (congrArg (· + (word m B (e + 8 * k)).toNat * (2 ^ 64) ^ k) ih).trans
      (congrArg (wv m B e k + ·) ((Nat.mul_comm _ _).trans
        (congrArg (· * (word m B (e + 8 * k)).toNat) (Nat.pow_mul 2 64 k).symm)))

theorem blockValue_words (m : Mem) (B : Addr) (e : Nat) :
    blockValue (fun i => word m B (e + 8 * i)) = wv m B e 8 := value_words m B e 8

theorem wv_radix_add (m : Mem) (B : Addr) (e n k : Nat) :
    wv m B e (n + k) = wv m B e n + (2 ^ 64) ^ n * wv m B (e + 8 * n) k :=
  (wv_add m B e n k).trans
    (congrArg (fun r => wv m B e n + r * wv m B (e + 8 * n) k) (Nat.pow_mul 2 64 n))

theorem word_flag (v : Word) (hv : v.toNat ≤ 1) : ∃ p : Bool, v = BitVec.ofNat 64 p.toNat := by
  rcases (by omega_using [hv] : v.toNat = 0 ∨ v.toNat = 1) with h | h
  · exact ⟨false, BitVec.eq_of_toNat_eq h⟩
  · exact ⟨true, BitVec.eq_of_toNat_eq h⟩

end VG.Proof.Bignum.AArch64.BlockedRedc
