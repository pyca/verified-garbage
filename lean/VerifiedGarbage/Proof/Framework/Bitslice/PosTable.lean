module

public import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# The position-table domain: bitwise circuits with per-position constants

Like the truth-table domain (`Table.lean`), for code that combines words only
with `xor`, `and` and `or`, but whose constants may differ from one bit
position to another (a table lookup that holds a different table in each
lane): an abstract value holds a truth table of `N` rows for each of the `w`
positions, the table of position `p` in bits `N p` to `N p + N - 1`
(`blocks`). A constant word is, at position `p`, the constant table of its
bit `p`. `PosRel N cs` relates the tables to a concrete word on the inputs
`cs p` of each position `p`, so one check of the tables proves what the code
computes at every position, for every input.
-/

@[expose] public section

namespace VG.Bitslice

/-- The tables `f p` of `N` rows at the positions `p < n`. -/
def blocks (N : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => blocks N f p ||| f p <<< (N * p)

theorem testBit_blocks {N : Nat} {f : Nat → Nat} (hf : ∀ p, f p < 2 ^ N) (n p c : Nat)
    (hc : c < N) : (blocks N f n).testBit (N * p + c) = (decide (p < n) && (f p).testBit c) := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    rw [blocks, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy p n with h | h | h
    · have hle : ¬ N * n ≤ N * p + c := by
        have := Nat.mul_le_mul_left N (show p + 1 ≤ n by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega
      simp [h, hle, show p < n + 1 by omega]
    · subst h
      simp [show N * p + c - N * p = c by omega]
    · have h1 : N * (n + 1) ≤ N * p := Nat.mul_le_mul_left N h
      rw [Nat.mul_add, Nat.mul_one] at h1
      have h2 : (f n).testBit (N * p + c - N * n) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf n)
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [show ¬ p < n by omega, show ¬ p < n + 1 by omega, h2]

/-- The constant word `v`: at each position, the table of its bit. -/
def spreadConst (w N v : Nat) : Nat := blocks N (fun p => if v.testBit p then 2 ^ N - 1 else 0) w

/-- The table `t` at every position. -/
def everywhere (w N t : Nat) : Nat := blocks N (fun _ => t) w

/-- Tables of `N` rows at `w` positions: rotations and shifts move bits
between positions, which the tables cannot follow. -/
def posTables (w N : Nat) : Dom Nat w where
  xor a b := some (a ^^^ b)
  and a b := some (a &&& b)
  or a b := some (a ||| b)
  ror _ _ := none
  shr _ _ := none
  const v := some (spreadConst w N v.toNat)

/-- Row `cs p` of the table of each position `p` is bit `p` of the word. -/
def PosRel {w : Nat} (N : Nat) (cs : Nat → Nat) (a : Nat) (x : BitVec w) : Prop :=
  ∀ p < w, a.testBit (N * p + cs p) = x.getLsbD p

theorem testBit_spreadConst {w N v p c : Nat} (hp : p < w) (hc : c < N) :
    (spreadConst w N v).testBit (N * p + c) = v.testBit p := by
  rw [spreadConst, testBit_blocks (fun p => by have := Nat.two_pow_pos N; split <;> omega) w p c hc]
  simp only [hp, decide_true, Bool.true_and]
  split
  · rename_i h; rw [h, Nat.testBit_two_pow_sub_one]; simp [hc]
  · rename_i h; simp only [Nat.zero_testBit]; simpa using h

theorem testBit_everywhere {w N t p c : Nat} (ht : t < 2 ^ N) (hp : p < w) (hc : c < N) :
    (everywhere w N t).testBit (N * p + c) = t.testBit c := by
  rw [everywhere, testBit_blocks (fun _ => ht) w p c hc]
  simp [hp]

theorem posTables_sound {w N : Nat} {cs : Nat → Nat} (hcs : ∀ p < w, cs p < N) :
    (posTables w N).Sound (PosRel N cs) where
  xor ha hb h p hp := by
    simp only [posTables, Option.some.injEq] at h; subst h
    rw [Nat.testBit_xor, BitVec.getLsbD_xor, ha p hp, hb p hp]
  and ha hb h p hp := by
    simp only [posTables, Option.some.injEq] at h; subst h
    rw [Nat.testBit_and, BitVec.getLsbD_and, ha p hp, hb p hp]
  or ha hb h p hp := by
    simp only [posTables, Option.some.injEq] at h; subst h
    rw [Nat.testBit_or, BitVec.getLsbD_or, ha p hp, hb p hp]
  ror _ h := by cases h
  shr _ h := by cases h
  const {v a} h p hp := by
    simp only [posTables, Option.some.injEq] at h; subst h
    rw [testBit_spreadConst hp (hcs p hp), BitVec.testBit_toNat]

theorem posRel_fun {w N : Nat} {cs : Nat → Nat} (a : Nat) (x y : BitVec w)
    (hx : PosRel N cs a x) (hy : PosRel N cs a y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [← hx p hp, ← hy p hp]

end VG.Bitslice
