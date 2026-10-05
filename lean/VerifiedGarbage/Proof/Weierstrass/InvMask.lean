import VerifiedGarbage.Proof.Mont.Words

/-!
# Inversion by divsteps: masks and signs of numbers of words

What the inversions of every target say about their numbers of words in
memory, apart from any ISA: masks (`IsMask`, `masked`), the sign of a
number's top word (`sgnW`, `sgn_iff`), the arithmetic shift by 59 of two
words (`shr_arith`) and a number sign-extended by a word (`sext`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Proof.Mont

/-- Words `0 … a + b` of a number: the first `a`, then `b` more. -/
theorem wordsVal_split (m : Mem) (base : Addr) (d a : Nat) :
    ∀ b, wordsVal m base d (a + b) = wordsVal m base d a + 2 ^ (64 * a) * wordsVal m base (d + 8 * a) b
  | 0 => by simp [wordsVal]
  | b + 1 => by
    rw [← Nat.add_assoc, wordsVal_succ_top, wordsVal_split m base d a b, wordsVal_succ_top m base (d + 8 * a) b,
      show d + 8 * a + 8 * b = d + 8 * (a + b) by omega, show 64 * (a + b) = 64 * a + 64 * b by omega, Nat.pow_add,
      Nat.mul_add (2 ^ (64 * a)), ← Nat.mul_assoc (2 ^ (64 * a))]
    omega

/-- A mask: all ones or zero. -/
def IsMask (x : BitVec 64) : Prop := x = 0 ∨ x = BitVec.allOnes 64

/-- `[src] & m` word by word, as a number. -/
def masked (m : BitVec 64) (v : Nat) : Nat := if m = BitVec.allOnes 64 then v else 0

theorem and_mask {x m : BitVec 64} (hm : IsMask m) : (x &&& m).toNat = masked m x.toNat := by
  unfold masked
  rcases hm with rfl | rfl
  · simp only [show (0 : BitVec 64) ≠ BitVec.allOnes 64 by decide, ↓reduceIte]; simp
  · simp only [↓reduceIte, BitVec.and_allOnes]

theorem masked_add (m : BitVec 64) (a A b : Nat) : masked m (a + A * b) = masked m a + A * masked m b := by
  unfold masked; split <;> simp

theorem masked_le (m : BitVec 64) (v : Nat) : masked m v ≤ v := by
  unfold masked; split <;> omega

/-- A word's sign, as a word: all ones if its top bit is set. -/
def sgnW (x : BitVec 64) : Nat := if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0

/-- Words `0 … j` of `X / 2^59`: from word `j` of `X`, and the next. -/
theorem shr_arith (j V s t : Nat) (hV : V < 2 ^ (64 * j)) :
    ((V + 2 ^ (64 * j) * s + 2 ^ (64 * j) * 2 ^ 64 * t) / 2 ^ 59) % (2 ^ (64 * j) * 2 ^ 64) =
      ((V + 2 ^ (64 * j) * s) / 2 ^ 59) % 2 ^ (64 * j) + 2 ^ (64 * j) * ((s / 2 ^ 59 + 2 ^ 5 * t) % 2 ^ 64) := by
  generalize 2 ^ (64 * j) = A at *
  have hA0 : 0 < A := by omega
  have e1 : A * 2 ^ 64 * t = 2 ^ 59 * (A * (2 ^ 5 * t)) := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl, Nat.mul_comm A, Nat.mul_assoc, Nat.mul_assoc,
      Nat.mul_left_comm A]
  have e2 : (V + A * s) / A = s := by
    rw [Nat.add_mul_div_left _ _ hA0, Nat.div_eq_of_lt hV, Nat.zero_add]
  rw [e1, Nat.add_mul_div_left _ _ (by decide), Nat.mod_mul, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ hA0, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 59), ← Nat.div_div_eq_div_mul, e2]

/-- `[src]` (`L` words) sign-extended by a word. -/
def sext (m : Mem) (base : Addr) (src L : Nat) : Nat :=
  wordsVal m base src L + 2 ^ (64 * L) * sgnW (word m base (src + 8 * (L - 1)))

/-- A number's top word. -/
theorem top_word (m : Mem) (base : Addr) (d n : Nat) :
    (word m base (d + 8 * n)).toNat = wordsVal m base d (n + 1) / 2 ^ (64 * n) := by
  rw [wordsVal_succ_top, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wordsVal_lt _ _ _ _), Nat.zero_add]

/-- Its sign: the top half. -/
theorem sgn_iff (m : Mem) (base : Addr) (d n : Nat) :
    2 ^ 63 ≤ (word m base (d + 8 * n)).toNat ↔ 2 ^ (64 * n) * 2 ^ 63 ≤ wordsVal m base d (n + 1) := by
  rw [top_word, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.mul_comm (2 ^ 63)]

theorem masked_sgn {m x : BitVec 64} (h : m.toNat = sgnW x) (v : Nat) :
    masked m v = if 2 ^ 63 ≤ x.toNat then v else 0 := by
  unfold masked sgnW at *
  by_cases hx : 2 ^ 63 ≤ x.toNat
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hx)] at h ⊢
    have : m = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_allOnes])
    rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)] at h ⊢
    have : m ≠ BitVec.allOnes 64 := fun e => by rw [e, BitVec.toNat_allOnes] at h; exact absurd h (by decide)
    rw [ite_eq_right_of_eq_false _ _ (eq_false this)]

theorem sgnW_top (m : Mem) (base : Addr) (d n : Nat) :
    sgnW (word m base (d + 8 * n)) =
      if 2 ^ (64 * n) * 2 ^ 63 ≤ wordsVal m base d (n + 1) then 2 ^ 64 - 1 else 0 := by
  unfold sgnW; simp only [sgn_iff]

theorem masked_top {x : BitVec 64} {m : Mem} {base : Addr} {d n : Nat}
    (h : x.toNat = sgnW (word m base (d + 8 * n))) (v : Nat) :
    masked x v = if 2 ^ (64 * n) * 2 ^ 63 ≤ wordsVal m base d (n + 1) then v else 0 := by
  rw [masked_sgn h]; simp only [sgn_iff]

/-- `2^64 [x]` modulo `2^(64 K)` reads only `K - 1` of `[x]`'s words. -/
theorem shifted_cong (m : Mem) (base : Addr) (x : Nat) {k K : Nat} (hk : K - 1 ≤ k) (hK : 1 ≤ K) :
    ((2 ^ 64 * wordsVal m base x (K - 1) : Nat) : Int) % ((2 ^ (64 * K) : Nat) : Int) =
      ((2 ^ 64 * wordsVal m base x k : Nat) : Int) % ((2 ^ (64 * K) : Nat) : Int) := by
  rw [← Int.natCast_emod, ← Int.natCast_emod]
  refine congrArg (Nat.cast : Nat → Int) ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = K - 1 + j := ⟨k - (K - 1), by omega⟩
  rw [wordsVal_split, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, show 64 + 64 * (K - 1) = 64 * K by omega,
    Nat.add_mul_mod_self_left]

end VG.Proof.Weierstrass
