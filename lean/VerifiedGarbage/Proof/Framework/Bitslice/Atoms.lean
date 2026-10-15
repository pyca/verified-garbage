module

public import VerifiedGarbage.Proof.Framework.Bitslice.Diag
public import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# Words of atoms, for checking linear layers

The lane domain (`Bitslice.lanes`) evaluates straight-line code that only
moves and XORs bits of 64-bit words, and masks them with constants, on
input words given as atoms: bit `t` of input word `i` is atom `64 i + t`
(`w i + t` for words of `w` bits, `inWordW`). An output word whose bit `p`
is the XOR of the atoms `g p` is related to the machine's word when bit `p`
of it is the XOR of the input bits `g p` (`outWord_rel`, `outWordW_rel`). Each ISA's `Framework/<ISA>/Linear.lean` runs its
evaluator with these.
-/

@[expose] public section

namespace VG.Bitslice

/-- The `w`-bit word whose bit `p` is the XOR of the atoms `g p`. -/
def outWordW (w : Nat) (g : Nat → List Nat) : Nat × Nat := (0, mk w g w)

/-- Input word `i`: bit `t` is atom `64 i + t`. -/
def inWord (i : Nat) : Nat × Nat := inWordW 64 i

/-- The word whose bit `p` is the XOR of the atoms `g p`. -/
def outWord (g : Nat → List Nat) : Nat × Nat := outWordW 64 g

/-- Bit `a % w` of word `a / w`. -/
def bitOf {w : Nat} (W : Nat → BitVec w) (a : Nat) : Bool := (W (a / w)).getLsbD (a % w)

/-- The XOR of the bits `l` of the words `W`. -/
def xorBits {w : Nat} (W : Nat → BitVec w) (l : List Nat) : Bool :=
  l.foldr (fun a b => bitOf W a ^^ b) false

@[simp] theorem xorBits_nil {w : Nat} (W : Nat → BitVec w) : xorBits W [] = false := rfl

@[simp] theorem xorBits_cons {w : Nat} (W : Nat → BitVec w) (a : Nat) (l : List Nat) :
    xorBits W (a :: l) = (bitOf W a ^^ xorBits W l) := rfl

theorem bitOf_word {w : Nat} (W : Nat → BitVec w) (i t : Nat) (ht : t < w) :
    bitOf W (w * i + t) = (W i).getLsbD t := by
  simp only [bitOf]
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt ht]

/-- The assignment of the atoms below `N` given by the words `W`. -/
def assign {w : Nat} (W : Nat → BitVec w) (N : Nat) : Nat := tableOf (bitOf W) N

theorem xorA_assign {w : Nat} (W : Nat → BitVec w) {N : Nat} {l : List Nat} (hl : ∀ a ∈ l, a < N) :
    xorA (assign W N) l = xorBits W l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [xorA, List.foldr_cons, xorBits_cons] at ih ⊢
    rw [ih fun b hb => hl b (by simp [hb]), assign, testBit_tableOf]
    simp [hl a (by simp)]

theorem inWordW_rel {w k : Nat} (W : Nat → BitVec w) {i : Nat} (hi : w * i + w ≤ 2 ^ k) :
    LaneRel k (assign W (2 ^ k)) (inWordW w i) (W i) := by
  refine ⟨Nat.two_pow_pos _, fun q hq => ?_⟩
  simp only [inWordW_eq_mk, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hq (Nat.le_refl _) _ (fun q' hq' a ha => by
      simp at ha; have := lane_lt (n := i + 1) (w := w) (Nat.lt_succ_self i) hq'
      rw [Nat.mul_succ] at this; omega),
    xorA_assign W (by
      intro a ha; simp at ha; have := lane_lt (n := i + 1) (w := w) (Nat.lt_succ_self i) hq
      rw [Nat.mul_succ] at this; omega)]
  simp [hq, bitOf_word W i q hq]

theorem outWordW_rel {w k : Nat} {W : Nat → BitVec w} {g : Nat → List Nat} {x : BitVec w}
    (hg : ∀ p < w, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (outWordW w g) x) :
    ∀ p < w, x.getLsbD p = xorBits W (g p) := by
  intro p hp
  rw [h.2 p hp]
  simp only [outWordW, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

/-- `outWordW_rel`, with the output word bounded instead of its atoms: an
evaluator compares the value it computed with `outWordW w g` and bounds that
value, rather than evaluating every `g p` again to bound its atoms. An atom
from `2 ^ k` on that cancels out (it appears an even number of times in
`g p`) leaves the value below `2 ^ (w 2 ^ k)`, and its bits cancel out of
`xorBits` too. -/
theorem outWordW_rel_of_lt {w k : Nat} {W : Nat → BitVec w} {g : Nat → List Nat} {x : BitVec w}
    (hb : mk w g w < 2 ^ (w * 2 ^ k)) (h : LaneRel k (assign W (2 ^ k)) (outWordW w g) x) :
    ∀ p < w, x.getLsbD p = xorBits W (g p) := by
  intro p hp
  -- A bound on every atom of `g` below `w`.
  have hM : ∀ q < w, ∀ a ∈ g q, a < 2 ^ k + (((List.range w).flatMap g).sum + 1) := by
    intro q hq a ha
    have : a ≤ ((List.range w).flatMap g).sum :=
      le_sum_of_mem (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, ha⟩)
    exact Nat.lt_of_le_of_lt this (Nat.lt_add_left _ (Nat.lt_succ_self _))
  rw [h.2 p hp]
  simp only [outWordW, Nat.zero_testBit, Bool.false_xor]
  rw [← xorA_assign W (hM p hp), ← (Bool.true_and _ : (true && xorA _ (g p)) = _),
    ← decide_eq_true hp, ← par_mk hp (Nat.le_refl _) _ hM, par_high hb hp]
  refine par_congr_assign fun a ha => ?_
  simp only [assign, testBit_tableOf, ha, decide_true, Bool.true_and,
    show a < 2 ^ k + (((List.range w).flatMap g).sum + 1) by omega]

theorem inWord_rel {k : Nat} (W : Nat → BitVec 64) {i : Nat} (hi : 64 * i + 64 ≤ 2 ^ k) :
    LaneRel k (assign W (2 ^ k)) (inWord i) (W i) :=
  inWordW_rel W hi

theorem outWord_rel {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {x : BitVec 64}
    (hg : ∀ p < 64, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (outWord g) x) :
    ∀ p < 64, x.getLsbD p = xorBits W (g p) :=
  outWordW_rel hg h

/-- An evaluator's value `v` for an output is the word `outWordW w g`, below
`2 ^ (w 2 ^ k)` (`outWordW_rel_of_lt`). The kernel evaluates `g` once, for
`outWordW w g`; a bound on the atoms of every `g p` would evaluate them
again. -/
def outOkW (w k : Nat) (v : Option (Nat × Nat)) (g : Nat → List Nat) : Bool :=
  match v with
  | some v => v == outWordW w g && decide (v.2 < 2 ^ (w * 2 ^ k))
  | none => false

/-- `outOkW` for words of 64 bits. -/
def outOk (k : Nat) (v : Option (Nat × Nat)) (g : Nat → List Nat) : Bool := outOkW 64 k v g

theorem outOkW_spec {w k : Nat} {v : Option (Nat × Nat)} {g : Nat → List Nat}
    (h : outOkW w k v g = true) : v = some (outWordW w g) ∧ mk w g w < 2 ^ (w * 2 ^ k) := by
  cases v with
  | none => cases h
  | some v =>
    simp only [outOkW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, h⟩

theorem outOk_spec {k : Nat} {v : Option (Nat × Nat)} {g : Nat → List Nat}
    (h : outOk k v g = true) : v = some (outWord g) ∧ mk 64 g 64 < 2 ^ (64 * 2 ^ k) :=
  outOkW_spec h

theorem outWord_rel_of_lt {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {x : BitVec 64}
    (hb : mk 64 g 64 < 2 ^ (64 * 2 ^ k)) (h : LaneRel k (assign W (2 ^ k)) (outWord g) x) :
    ∀ p < 64, x.getLsbD p = xorBits W (g p) :=
  outWordW_rel_of_lt hb h

end VG.Bitslice
