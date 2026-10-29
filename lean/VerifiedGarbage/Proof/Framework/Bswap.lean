module

public import VerifiedGarbage.Proof.Framework.Mem

/-!
# Byte reversal of a little-endian load is a big-endian load

Each ISA model defines its byte-reversal instructions (x86's `bswap`, Arm's
`rev`) as `byteRev32` and `byteRev64` are defined here, so the lemmas about
them are stated once, for every target.
-/

@[expose] public section

namespace VG

/-- The bytes of a 32-bit word in reverse order. -/
def byteRev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- The bytes of a 64-bit word in reverse order. -/
def byteRev64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

theorem getLsbD_cat4 (b0 b1 b2 b3 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec (8 + 8 + 8 + 8)).getLsbD i =
      if i < 8 then b3.getLsbD i else if i < 16 then b2.getLsbD (i - 8)
      else if i < 24 then b1.getLsbD (i - 16) else b0.getLsbD (i - 24) := by
  simp only [BitVec.getLsbD_append]
  repeat' split
  all_goals first | omega | rfl

/-- The low byte of `y ++ a`. -/
theorem extractLsb'_append_byte_lo {w : Nat} (y : BitVec w) (a : BitVec 8) :
    (y ++ a).extractLsb' 0 8 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, hi]

/-- A byte of `y ++ a` above the low one. -/
theorem extractLsb'_append_byte_hi {w : Nat} (y : BitVec w) (a : BitVec 8) {k : Nat} (hk : 8 ≤ k) :
    (y ++ a).extractLsb' k 8 = y.extractLsb' (k - 8) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬k + i < 8 by omega, ite_false]
  exact congrArg _ (by omega)

theorem byteRev32_bytes (b0 b1 b2 b3 : BitVec 8) :
    byteRev32 ((0#0 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 32) = (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) := by
  simp (disch := decide) only [byteRev32, BitVec.setWidth_eq, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceSub]

/-- A 32-bit load followed by a byte reversal reads the four bytes big-endian. -/
theorem byteRev32_readW (m : Mem) (a : Addr) :
    byteRev32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  byteRev32_bytes _ _ _ _

/-- The bytes of a byte-reversed word, from the least significant, are the
word's from the most significant. -/
theorem byteRev32_extract (w : BitVec 32) :
    (List.range 4).map (fun j => (byteRev32 w).extractLsb' (8 * j) 8) =
      [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp (disch := decide) only [byteRev32, Nat.mul_zero, Nat.reduceMul, extractLsb'_append_byte_lo,
      extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

theorem byteRev64_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    byteRev64 ((0#0 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp (disch := decide) only [byteRev64, BitVec.setWidth_eq, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceSub]

/-- A 64-bit load followed by a byte reversal reads the eight bytes big-endian. -/
theorem byteRev64_readW (m : Mem) (a : Addr) :
    byteRev64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  byteRev64_bytes _ _ _ _ _ _ _ _

/-- Bit `r` of byte `k` of `x ++ b`, for a byte `b`. -/
theorem getLsbD_append_byte {w : Nat} (x : BitVec w) (b : BitVec 8) (k : Nat) {r : Nat} (hr : r < 8) :
    (x ++ b).getLsbD (8 * k + r) = if k = 0 then b.getLsbD r else x.getLsbD (8 * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  cases k with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, hr, ite_true]
  | succ k =>
    rw [show 8 * (k + 1) + r - 8 = 8 * k + r by omega]
    simp only [show ¬ 8 * (k + 1) + r < 8 by omega, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

/-- Bit `i` of a byte-reversed 32-bit word. The byte's index is a literal in each case,
so every `if` and subtraction reduces without `omega`. -/
theorem byteRev32_getLsbD (w : BitVec 32) {i : Nat} (hi : i < 32) :
    (byteRev32 w).getLsbD i = w.getLsbD (8 * (3 - i / 8) + i % 8) := by
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 8 ∧ i = 8 * a + b :=
    ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 8).symm⟩
  have ha : a < 4 := by omega
  rw [show (8 * a + b) / 8 = a by omega, show (8 * a + b) % 8 = b by omega]
  unfold byteRev32
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    simp only [getLsbD_append_byte _ _ _ hb, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte]
    simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, Nat.reduceMul, Nat.zero_add]

/-- Bit `i` of a byte-reversed 64-bit word (as `byteRev32_getLsbD`). -/
theorem byteRev64_getLsbD (w : BitVec 64) {i : Nat} (hi : i < 64) :
    (byteRev64 w).getLsbD i = w.getLsbD (8 * (7 - i / 8) + i % 8) := by
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 8 ∧ i = 8 * a + b :=
    ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 8).symm⟩
  have ha : a < 8 := by omega
  rw [show (8 * a + b) / 8 = a by omega, show (8 * a + b) % 8 = b by omega]
  unfold byteRev64
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [getLsbD_append_byte _ _ _ hb, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte]
    simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, Nat.reduceMul, Nat.zero_add]

end VG
