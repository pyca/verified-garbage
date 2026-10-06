import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.WordDef
import Mathlib.Data.BitVec

/-!
# Divsteps on 64-bit words

A divstep with its matrix on words (`wstep`), without branches: with the
masks `B` (all ones if `g` is odd) and `S = B` and `d ≥ 0`, `(x ^ S) - S` is
`-x` or `x`, so `g + ((f ^ S) - S) & B` is `g - f`, `g + f` or `g`, and
`f + (g' & S)` swaps. On words that hold `d` and the matrix and agree with
`f` and `g` on their low `k + 1` bits, it gives the next state, agreeing on
`k` bits (`wstep_rel`); so `n ≤ 64` steps from the low words of `f` and `g`
give `d` and the matrix of `n` divsteps (`wsteps_rel`).
-/

namespace VG.Proof.Divstep

/-- Words holding `d` and the matrix of `t`, and `f`, `g` modulo `2^k`. -/
def WSt.rel (w : WSt) (t : MSt) (k : Nat) : Prop :=
  w.D = BitVec.ofInt 64 t.d ∧ w.U = BitVec.ofInt 64 t.u ∧ w.V = BitVec.ofInt 64 t.v ∧
    w.Q = BitVec.ofInt 64 t.q ∧ w.R = BitVec.ofInt 64 t.r ∧
    (w.F.toNat : Int) % 2 ^ k = t.f % 2 ^ k ∧ (w.G.toNat : Int) % 2 ^ k = t.g % 2 ^ k

theorem ofInt_sub' (a b : Int) : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
  rw [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem shl1 (x : BitVec 64) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1; omega

theorem ofInt_two_mul (a : Int) : BitVec.ofInt 64 (2 * a) = BitVec.ofInt 64 a <<< 1 := by
  rw [shl1, two_mul, BitVec.ofInt_add]

/-- Congruence modulo `2^k` (`k ≤ 64`) of a word's value and an integer it is
congruent to modulo `2^64`. -/
theorem toNat_cong {x : BitVec 64} {a : Int} {k : Nat} (hk : k ≤ 64)
    (h : (x.toNat : Int) % 2 ^ 64 = a % 2 ^ 64) : (x.toNat : Int) % 2 ^ k = a % 2 ^ k := by
  have hd : (2 : Int) ^ k ∣ 2 ^ 64 := pow_dvd_pow 2 hk
  rw [← Int.emod_emod_of_dvd _ hd, h, Int.emod_emod_of_dvd _ hd]

theorem lowered {x : BitVec 64} {a : Int} {k : Nat} (h : (x.toNat : Int) % 2 ^ (k + 1) = a % 2 ^ (k + 1)) :
    (x.toNat : Int) % 2 ^ k = a % 2 ^ k := by
  have hd : (2 : Int) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  rw [← Int.emod_emod_of_dvd _ hd, h, Int.emod_emod_of_dvd _ hd]

/-- `x - y` as an integer modulo `2^64`. -/
theorem toNat_sub_cong (x y : BitVec 64) :
    ((x - y).toNat : Int) % 2 ^ 64 = ((x.toNat : Int) - y.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]
  have := y.isLt
  push_cast
  rw [Int.emod_emod_of_dvd _ (by norm_num)]
  omega

theorem toNat_add_cong (x y : BitVec 64) :
    ((x + y).toNat : Int) % 2 ^ 64 = ((x.toNat : Int) + y.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add]; push_cast; rw [Int.emod_emod_of_dvd _ (by norm_num)]

/-- Halving a word whose value is congruent to an even integer. -/
theorem half_word {x : BitVec 64} {a : Int} {k : Nat} (hk : k + 1 ≤ 64)
    (h : (x.toNat : Int) % 2 ^ (k + 1) = a % 2 ^ (k + 1)) (ha : a % 2 = 0) :
    ((x >>> 1).toNat : Int) % 2 ^ k = (a / 2) % 2 ^ k := by
  have hx2 : (x.toNat : Int) % 2 = 0 := by
    have := congrArg (· % 2) h
    simp only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) from dvd_pow_self 2 (by omega))] at this
    omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have : ((x.toNat / 2 : Nat) : Int) = (x.toNat : Int) / 2 := by push_cast; rfl
  rw [this]
  exact half_cong h hx2 ha

/-! The three kinds of step, on words. -/

theorem c_allOnes : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
theorem c_one : (1 : BitVec 64) - 1 = 0 := by decide
theorem c_zero : (0 : BitVec 64) - 0 = 0 := by decide
theorem and0 (x : BitVec 64) : x &&& 0 = 0 := by simp
theorem and0' (x : BitVec 64) : 0 &&& x = 0 := by simp
theorem xor0 (x : BitVec 64) : x ^^^ 0 = x := by simp
theorem ofInt_two : BitVec.ofInt 64 2 = 2 := by decide
theorem two64 : (2#64 : BitVec 64) = 2 := rfl

theorem sub0 (x : BitVec 64) : x - 0 = x := by simp
theorem add0 (x : BitVec 64) : x + 0 = x := by simp

theorem neg_sel (X : BitVec 64) : (X ^^^ BitVec.allOnes 64) - BitVec.allOnes 64 = -X := by
  rw [BitVec.xor_allOnes, BitVec.neg_eq_not_add]
  have : BitVec.allOnes 64 = -1 := by decide
  rw [this, BitVec.sub_neg]; rfl

/-- `g` odd and `d ≥ 0`: the swap. -/
theorem wstep_swap (w : WSt) (hB : w.G &&& 1 = 1) (hS : w.D >>> 63 = 0) :
    wstep w = ⟨-w.D + 2, w.G, (w.G - w.F) >>> 1, w.Q <<< 1, w.R <<< 1, w.Q - w.U, w.R - w.V⟩ := by
  simp only [wstep, hB, hS, c_allOnes, BitVec.and_allOnes, neg_sel, WSt.mk.injEq]
  refine ⟨trivial, by ring, by rw [show w.G + -w.F = w.G - w.F by ring], by rw [show w.U + (w.Q + -w.U) = w.Q by ring],
    by rw [show w.V + (w.R + -w.V) = w.R by ring], by ring, by ring⟩

/-- `g` odd and `d < 0`: `g + f`. -/
theorem wstep_odd (w : WSt) (hB : w.G &&& 1 = 1) (hS : w.D >>> 63 = 1) :
    wstep w = ⟨w.D + 2, w.F, (w.G + w.F) >>> 1, w.U <<< 1, w.V <<< 1, w.Q + w.U, w.R + w.V⟩ := by
  simp only [wstep, hB, hS, c_allOnes, c_one, and0, xor0, BitVec.and_allOnes, sub0, add0]

/-- `g` even. -/
theorem wstep_even (w : WSt) (hB : w.G &&& 1 = 0) :
    wstep w = ⟨w.D + 2, w.F, w.G >>> 1, w.U <<< 1, w.V <<< 1, w.Q, w.R⟩ := by
  simp only [wstep, hB, and0, xor0, sub0, add0]

/-- `G & 1` is `G`'s low bit. -/
theorem and_one_word (x : BitVec 64) : x &&& 1 = if x.toNat % 2 = 1 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split <;> simp_all

/-- `D >>> 63` is `D`'s sign, for `|d| < 2^63`. -/
theorem sign_word {d : Int} (hd : |d| < 2 ^ 62) : BitVec.ofInt 64 d >>> 63 = if d < 0 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  rw [abs_lt] at hd
  push_cast
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- A divstep on words. -/
theorem wstep_rel {w : WSt} {t : MSt} {k : Nat} (hk : k + 1 ≤ 64) (h : w.rel t (k + 1))
    (hd : |t.d| < 2 ^ 62) (hf : t.f % 2 = 1) : (wstep w).rel (mstep t) k := by
  obtain ⟨hD, hU, hV, hQ, hR, hF, hG⟩ := h
  have hpar : ∀ x : BitVec 64, ∀ a : Int, (x.toNat : Int) % 2 ^ (k + 1) = a % 2 ^ (k + 1) →
      (x.toNat : Int) % 2 = a % 2 := fun x a hx => by
    have := congrArg (· % 2) hx
    simpa only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) from dvd_pow_self 2 (by omega))] using this
  have gG := hpar _ _ hG
  have hS := sign_word hd
  rw [← hD] at hS
  have hB := and_one_word w.G
  have hd' : (2 : Int) ^ (k + 1) ∣ 2 ^ 64 := pow_dvd_pow 2 hk
  unfold mstep
  by_cases hg : t.g % 2 = 1
  · rw [ite_t (show w.G.toNat % 2 = 1 by omega)] at hB
    by_cases hd0 : 0 ≤ t.d
    · rw [ite_f (show ¬ t.d < 0 by omega)] at hS
      rw [wstep_swap w hB hS, ite_t ⟨hd0, hg⟩]
      refine ⟨?_, ?_, ?_, ?_, ?_, lowered hG, half_word hk ?_ (by omega)⟩
      · simp only; rw [hD, ofInt_sub', ofInt_two]; ring
      · simp only; rw [hQ, ofInt_two_mul]
      · simp only; rw [hR, ofInt_two_mul]
      · simp only; rw [hQ, hU, ofInt_sub']
      · simp only; rw [hR, hV, ofInt_sub']
      · rw [← Int.emod_emod_of_dvd _ hd', toNat_sub_cong, Int.emod_emod_of_dvd _ hd', Int.sub_emod, hG, hF,
          ← Int.sub_emod]
    · rw [ite_t (show t.d < 0 by omega)] at hS
      rw [wstep_odd w hB hS, ite_f (show ¬ (0 ≤ t.d ∧ t.g % 2 = 1) by omega)]
      refine ⟨?_, ?_, ?_, ?_, ?_, lowered hF, ?_⟩
      · simp only; rw [hD, BitVec.ofInt_add, BitVec.ofInt_ofNat, two64]; ring
      · simp only; rw [hU, ofInt_two_mul]
      · simp only; rw [hV, ofInt_two_mul]
      · simp only; rw [hQ, hU, hg, one_mul, BitVec.ofInt_add]
      · simp only; rw [hR, hV, hg, one_mul, BitVec.ofInt_add]
      · simp only; rw [hg, one_mul]
        refine half_word hk ?_ (by omega)
        rw [← Int.emod_emod_of_dvd _ hd', toNat_add_cong, Int.emod_emod_of_dvd _ hd', Int.add_emod, hG, hF,
          ← Int.add_emod]
  · have hg0 : t.g % 2 = 0 := by omega
    rw [ite_f (show ¬ w.G.toNat % 2 = 1 by omega)] at hB
    rw [wstep_even w hB, ite_f (show ¬ (0 ≤ t.d ∧ t.g % 2 = 1) by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_, lowered hF, ?_⟩
    · simp only; rw [hD, BitVec.ofInt_add, BitVec.ofInt_ofNat, two64]; ring
    · simp only; rw [hU, ofInt_two_mul]
    · simp only; rw [hV, ofInt_two_mul]
    · simp only; rw [hQ, hg0, zero_mul, add_zero]
    · simp only; rw [hR, hg0, zero_mul, add_zero]
    · simp only; rw [hg0, zero_mul, add_zero]; exact half_word hk hG hg0

/-- `n ≤ K` steps on words agreeing on `K ≤ 64` bits. -/
theorem wsteps_rel {w : WSt} {t : MSt} {K : Nat} (hK : K ≤ 64) (h : w.rel t K)
    (hd : |t.d| + 2 * K < 2 ^ 62) (hf : t.f % 2 = 1) : ∀ n ≤ K, (wsteps n w).rel (msteps n t) (K - n)
  | 0, _ => by simpa [wsteps, msteps] using h
  | n + 1, hn => by
    have ih := wsteps_rel hK h hd hf n (by omega)
    rw [wsteps_succ, msteps_succ]
    rw [show K - n = (K - (n + 1)) + 1 by omega] at ih
    refine wstep_rel (by omega) ih ?_ (msteps_f_odd hf n)
    have := msteps_d t n
    have : (2 * n : Int) ≤ 2 * K := by exact_mod_cast (by omega : 2 * n ≤ 2 * K)
    linarith

end VG.Proof.Divstep
