import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.PackedDef

/-!
# Packed divsteps on 64-bit words

The steps of a chunk on its matrix's rows `u P + v Q` and `q P + r Q`
modulo `2^64` (`PackedDef.lean`'s `pstep`), for `P ≡ f` and `Q ≡ g` modulo
`2^n`: each is `mstep`'s, doubled, with `g`'s parity at bit `j`
(`pstep_rel`, `psteps_rel`). The entries after `n` steps are at least
`-2^(n-1)` (`msteps_lo`, as `|u| + |v| ≤ 2^n` bounds them above), so for
`n ≤ 15` and `P`, `Q` below `2^15` plus `2^31` and `2^47` the rows' fields
give the entries (`pext_rel`). Steps from any matrix are the identity's
times it (`msteps_gen`), so a batch's matrix is its chunks' product.
-/

namespace VG.Proof.Divstep

/-! ## Steps from any matrix -/

theorem msteps_add (a b : Nat) (t : MSt) : msteps (a + b) t = msteps b (msteps a t) := by
  induction a generalizing t with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [Nat.succ_add, msteps, msteps, ih]

/-- `n` steps from a state with any matrix: the identity's `n` steps, their
matrix times the state's. -/
theorem msteps_gen (n : Nat) (t : MSt) :
    msteps n t =
      ⟨(msteps n (MSt.init t.d t.f t.g)).d, (msteps n (MSt.init t.d t.f t.g)).f,
        (msteps n (MSt.init t.d t.f t.g)).g,
        (msteps n (MSt.init t.d t.f t.g)).u * t.u + (msteps n (MSt.init t.d t.f t.g)).v * t.q,
        (msteps n (MSt.init t.d t.f t.g)).u * t.v + (msteps n (MSt.init t.d t.f t.g)).v * t.r,
        (msteps n (MSt.init t.d t.f t.g)).q * t.u + (msteps n (MSt.init t.d t.f t.g)).r * t.q,
        (msteps n (MSt.init t.d t.f t.g)).q * t.v + (msteps n (MSt.init t.d t.f t.g)).r * t.r⟩ := by
  induction n with
  | zero => simp only [msteps, MSt.init]; ring_nf
  | succ n ih =>
    rw [msteps_succ, msteps_succ, ih]
    generalize msteps n (MSt.init t.d t.f t.g) = m
    unfold mstep
    by_cases h : 0 ≤ m.d ∧ m.g % 2 = 1
    · rw [ite_t h, ite_t h]
      simp only [MSt.mk.injEq]
      refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_⟩ <;> ring
    · rw [ite_f h, ite_f h]
      simp only [MSt.mk.injEq]
      refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_⟩ <;> ring

/-! ## The entries' range -/

/-- After `n` steps from the identity the entries are at least `-2^(n-1)`,
and `u - q`, `v - r` at most `2^n`. -/
def MSt.lo (t : MSt) (n : Nat) : Prop :=
  -2 ^ n ≤ 2 * t.u ∧ -2 ^ n ≤ 2 * t.v ∧ -2 ^ n ≤ 2 * t.q ∧ -2 ^ n ≤ 2 * t.r ∧
    t.u - t.q ≤ 2 ^ n ∧ t.v - t.r ≤ 2 ^ n

theorem mstep_lo {t : MSt} {n : Nat} (hb : t.bnd n) (h : t.lo n) : (mstep t).lo (n + 1) := by
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := h
  have au := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg t.v)) b1)
  have av := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg t.u)) b1)
  have aq := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg t.r)) b2)
  have ar := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg t.q)) b2)
  unfold mstep MSt.lo
  rw [pow_succ]
  split
  · simp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rcases Int.emod_two_eq_zero_or_one t.g with hg | hg <;> simp only [hg, zero_mul, one_mul, add_zero] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem msteps_lo (d f g : Int) : ∀ n, (msteps n (MSt.init d f g)).lo n
  | 0 => by simp only [msteps, MSt.init, MSt.lo]; norm_num
  | n + 1 => by rw [msteps_succ]; exact mstep_lo (msteps_bnd d f g n) (msteps_lo d f g n)

/-! ## A packed step -/

theorem not_ofInt (d : Int) : ~~~BitVec.ofInt 64 d = BitVec.ofInt 64 (-d - 1) := by
  have h : ~~~BitVec.ofInt 64 d = -BitVec.ofInt 64 d - 1 := by
    rw [BitVec.neg_eq_not_add]; exact (BitVec.add_sub_cancel _ _).symm
  rw [h, ofInt_sub', BitVec.ofInt_neg]; rfl

theorem oadd (a b : Int) : BitVec.ofInt 64 a + BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) :=
  (BitVec.ofInt_add _ _).symm

theorem osub (a b : Int) : BitVec.ofInt 64 a - BitVec.ofInt 64 b = BitVec.ofInt 64 (a - b) :=
  (ofInt_sub' a b).symm

theorem otwo : (2 : BitVec 64) = BitVec.ofInt 64 2 := by decide
theorem omtwo : (-2 : BitVec 64) = BitVec.ofInt 64 (-2) := by decide

/-- A word congruent to `2^j b` modulo `2^(j + 1)`, shifted left by `63 - j`: `2^63 b`. -/
theorem shl_bit {X b : Int} {j : Nat} (hj : j ≤ 62) (hb : b = 0 ∨ b = 1)
    (h : X % 2 ^ (j + 1) = 2 ^ j * b) : ((BitVec.ofInt 64 X) <<< (63 - j)).toNat = 2 ^ 63 * b.toNat := by
  have hd : ((2 : Int) ^ (j + 1)) ∣ 2 ^ 64 := pow_dvd_pow 2 (by omega)
  have hm : (BitVec.ofInt 64 X).toNat % 2 ^ (j + 1) = 2 ^ j * b.toNat := by
    have hc : (((BitVec.ofInt 64 X).toNat % 2 ^ (j + 1) : Nat) : Int) = 2 ^ j * b := by
      push_cast; rw [toNat_ofInt64, Int.emod_emod_of_dvd _ hd, h]
    rcases hb with rfl | rfl
    · simp only [mul_zero, Nat.cast_eq_zero] at hc; rw [hc]; simp
    · simp only [mul_one] at hc; simp only [Int.toNat_one, mul_one]; exact_mod_cast hc
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have e : (2 : Nat) ^ 64 = 2 ^ (j + 1) * 2 ^ (63 - j) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_right, hm, mul_comm (2 ^ j), mul_assoc, ← pow_add, show j + (63 - j) = 63 by omega,
    mul_comm]

/-- `~d`'s word is at least `2^63` exactly for `d ≥ 0`. -/
theorem not_ofInt_ge {d : Int} (hd : |d| < 2 ^ 62) :
    2 ^ 63 ≤ (~~~BitVec.ofInt 64 d).toNat ↔ 0 ≤ d := by
  rw [BitVec.toNat_not]
  have hx := toNat_ofInt64 d
  have hl := (BitVec.ofInt 64 d).isLt
  rw [abs_lt] at hd
  by_cases h0 : 0 ≤ d
  · have : d % 2 ^ 64 = d := Int.emod_eq_of_lt h0 (by omega)
    omega
  · have : d % 2 ^ 64 = d + 2 ^ 64 := by
      rw [← Int.add_mul_emod_self_left d (2 ^ 64) 1, mul_one, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- A packed step is `mstep`'s, when the `g` row's bits below `j + 1` are `2^j g`'s. -/
theorem pstep_rel {t : MSt} {P Q : Int} {j : Nat} (hj : j ≤ 62) (hd : |t.d| < 2 ^ 62)
    (hG : (t.q * P + t.r * Q) % 2 ^ (j + 1) = 2 ^ j * (t.g % 2)) :
    pstep j (~~~BitVec.ofInt 64 t.d, BitVec.ofInt 64 (t.u * P + t.v * Q), BitVec.ofInt 64 (t.q * P + t.r * Q)) =
      (~~~BitVec.ofInt 64 (mstep t).d, BitVec.ofInt 64 ((mstep t).u * P + (mstep t).v * Q),
        BitVec.ofInt 64 ((mstep t).q * P + (mstep t).r * Q)) := by
  have hb := Int.emod_two_eq_zero_or_one t.g
  have hs := shl_bit hj hb hG
  have hE := not_ofInt_ge hd
  have hlt := (~~~BitVec.ofInt 64 t.d).isLt
  unfold pstep
  simp only
  rcases hb with hg | hg
  · -- `g` even: no swap.
    rw [hg] at hs
    simp only [Int.toNat_zero, mul_zero] at hs
    have h0 : (BitVec.ofInt 64 (t.q * P + t.r * Q)) <<< (63 - j) = 0 := BitVec.eq_of_toNat_eq (by rw [hs]; rfl)
    have hm : mstep t = ⟨2 + t.d, t.f, (t.g + t.g % 2 * t.f) / 2, 2 * t.u, 2 * t.v, t.q + t.g % 2 * t.u,
        t.r + t.g % 2 * t.v⟩ := by unfold mstep; rw [ite_f (show ¬ (0 ≤ t.d ∧ t.g % 2 = 1) by omega)]
    rw [ite_f (by rw [hs]; omega), ite_t h0, hm]
    simp only [hg, zero_mul, add_zero, Prod.mk.injEq]
    refine ⟨?_, ?_, trivial⟩
    · rw [not_ofInt, not_ofInt, otwo, osub]; congr 1; ring
    · rw [oadd]; congr 1; ring
  · rw [hg] at hs
    simp only [Int.toNat_one, mul_one] at hs
    have hne : ¬ (BitVec.ofInt 64 (t.q * P + t.r * Q)) <<< (63 - j) = 0 := fun h => by
      rw [h] at hs; simp at hs
    by_cases hd0 : 0 ≤ t.d
    · -- the swap
      have hm : mstep t = ⟨2 - t.d, t.g, (t.g - t.f) / 2, 2 * t.q, 2 * t.r, t.q - t.u, t.r - t.v⟩ := by
        unfold mstep; rw [ite_t ⟨hd0, hg⟩]
      rw [ite_t (by rw [hs]; have := hE.mpr hd0; omega), hm]
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · rw [not_ofInt, not_ofInt, omtwo, otwo, osub, osub]; congr 1; ring
      · rw [oadd]; congr 1; ring
      · rw [osub]; congr 1; ring
    · have hm : mstep t = ⟨2 + t.d, t.f, (t.g + t.g % 2 * t.f) / 2, 2 * t.u, 2 * t.v, t.q + t.g % 2 * t.u,
          t.r + t.g % 2 * t.v⟩ := by unfold mstep; rw [ite_f (show ¬ (0 ≤ t.d ∧ t.g % 2 = 1) by omega)]
      rw [ite_f (by rw [hs]; have := mt hE.mp hd0; omega), ite_f hne, hm]
      simp only [hg, one_mul, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · rw [not_ofInt, not_ofInt, otwo, osub]; congr 1; ring
      · rw [oadd]; congr 1; ring
      · rw [oadd]; congr 1; ring

/-- `x ≡ 2^j y` modulo `2^(j + 1)` is `2^j (y mod 2)`. -/
theorem pow_mul_emod_succ (j : Nat) (y : Int) : 2 ^ j * y % 2 ^ (j + 1) = 2 ^ j * (y % 2) := by
  rw [pow_succ, Int.mul_emod_mul_of_pos _ _ (by positivity)]

/-- `k ≤ n` packed steps from `P ≡ f` and `Q ≡ g` modulo `2^n` are `msteps`'. -/
theorem psteps_rel {d f g P Q : Int} {n : Nat} (hn : n ≤ 62) (hf : f % 2 = 1) (hd : |d| + 2 * n < 2 ^ 62)
    (hP : P % 2 ^ n = f % 2 ^ n) (hQ : Q % 2 ^ n = g % 2 ^ n) :
    ∀ k ≤ n, psteps k (~~~BitVec.ofInt 64 d, BitVec.ofInt 64 P, BitVec.ofInt 64 Q) =
      (~~~BitVec.ofInt 64 (msteps k (MSt.init d f g)).d,
        BitVec.ofInt 64 ((msteps k (MSt.init d f g)).u * P + (msteps k (MSt.init d f g)).v * Q),
        BitVec.ofInt 64 ((msteps k (MSt.init d f g)).q * P + (msteps k (MSt.init d f g)).r * Q))
  | 0, _ => by simp only [psteps, msteps, MSt.init, one_mul, zero_mul, add_zero, zero_add]
  | k + 1, hk => by
    rw [psteps, psteps_rel hn hf hd hP hQ k (by omega), msteps_succ]
    refine pstep_rel (by omega) ?_ ?_
    · have := msteps_d (MSt.init d f g) k
      rw [show (MSt.init d f g).d = d from rfl] at this
      have : (2 * k : Int) ≤ 2 * n := by exact_mod_cast (by omega : 2 * k ≤ 2 * n)
      linarith
    · obtain ⟨-, mg⟩ := msteps_mat (d := d) (g := g) hf k
      have hdv : (2 : Int) ^ (k + 1) ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      rw [← pow_mul_emod_succ, mg, ← Int.emod_emod_of_dvd _ hdv, ← Int.emod_emod_of_dvd (_ * f + _) hdv]
      congr 1
      rw [Int.add_emod, Int.mul_emod _ P, hP, ← Int.mul_emod, Int.mul_emod _ Q, hQ, ← Int.mul_emod, ← Int.add_emod]

/-! ## The entries from the rows -/

/-- For `n ≤ 15` steps, `0 ≤ a, b < 2^15`, entries at least `-2^14` and
`|u| + |v| ≤ 2^15`: the fields of `u (a + 2^31) + v (b + 2^47)`. -/
theorem pext_rel {u v : Int} {a b : Nat} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (hu : -2 ^ 14 ≤ u)
    (hv : -2 ^ 14 ≤ v) (huv : |u| + |v| ≤ 2 ^ 15) :
    pextLo (BitVec.ofInt 64 (u * (a + 2 ^ 31) + v * (b + 2 ^ 47))) = BitVec.ofInt 64 u ∧
      pextHi (BitVec.ofInt 64 (u * (a + 2 ^ 31) + v * (b + 2 ^ 47))) = BitVec.ofInt 64 v := by
  have au := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg v)) huv)
  have av := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg u)) huv)
  -- `L = u a + v b`, `|L| < 2^30`.
  have ha' : (a : Int) < 2 ^ 15 := by exact_mod_cast ha
  have hb' : (b : Int) < 2 ^ 15 := by exact_mod_cast hb
  have ha0 : (0 : Int) ≤ a := by positivity
  have hb0 : (0 : Int) ≤ b := by positivity
  have L1 : u * a + v * b < 2 ^ 30 := by
    have : u * a ≤ |u| * (2 ^ 15 - 1) := by
      calc u * a ≤ |u| * a := mul_le_mul_of_nonneg_right (le_abs_self u) ha0
        _ ≤ |u| * (2 ^ 15 - 1) := mul_le_mul_of_nonneg_left (by omega) (abs_nonneg u)
    have : v * b ≤ |v| * (2 ^ 15 - 1) := by
      calc v * b ≤ |v| * b := mul_le_mul_of_nonneg_right (le_abs_self v) hb0
        _ ≤ |v| * (2 ^ 15 - 1) := mul_le_mul_of_nonneg_left (by omega) (abs_nonneg v)
    linarith [abs_nonneg u, abs_nonneg v]
  have L2 : -2 ^ 30 < u * a + v * b := by
    have : -2 ^ 14 * (2 ^ 15 - 1) ≤ u * a := by
      calc -2 ^ 14 * (2 ^ 15 - 1) ≤ -2 ^ 14 * (a : Int) := by linarith
        _ ≤ u * a := mul_le_mul_of_nonneg_right hu ha0
    have : -2 ^ 14 * (2 ^ 15 - 1) ≤ v * b := by
      calc -2 ^ 14 * (2 ^ 15 - 1) ≤ -2 ^ 14 * (b : Int) := by linarith
        _ ≤ v * b := mul_le_mul_of_nonneg_right hv hb0
    linarith
  -- The sum with `pextC`, as fields.
  set A : Nat := (u * a + v * b + 2 ^ 30).toNat with hA
  set B : Nat := (u + 2 ^ 14).toNat with hB
  set C : Nat := (v + 2 ^ 14).toNat with hC
  have eA : (A : Int) = u * a + v * b + 2 ^ 30 := Int.toNat_of_nonneg (by linarith)
  have eB : (B : Int) = u + 2 ^ 14 := Int.toNat_of_nonneg (by linarith)
  have eC : (C : Int) = v + 2 ^ 14 := Int.toNat_of_nonneg (by linarith)
  have bA : A < 2 ^ 31 := by omega
  have bB : B < 2 ^ 16 := by omega
  have bC : C < 2 ^ 17 := by omega
  have hY : BitVec.ofInt 64 (u * (a + 2 ^ 31) + v * (b + 2 ^ 47)) + pextC =
      BitVec.ofNat 64 (A + B * 2 ^ 31 + C * 2 ^ 47) := by
    rw [pextC, show (2 ^ 30 + 2 ^ 45 + 2 ^ 61 : BitVec 64) = BitVec.ofInt 64 (2 ^ 30 + 2 ^ 45 + 2 ^ 61) by decide,
      oadd, ← BitVec.ofInt_natCast]
    congr 1; push_cast; rw [eA, eB, eC]; ring
  have hN : A + B * 2 ^ 31 + C * 2 ^ 47 < 2 ^ 64 := by omega
  have toN : (BitVec.ofNat 64 (A + B * 2 ^ 31 + C * 2 ^ 47)).toNat = A + B * 2 ^ 31 + C * 2 ^ 47 :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  have s16 : (16384 : BitVec 64) = BitVec.ofInt 64 (2 ^ 14) := by decide
  constructor
  · rw [pextLo, hY]
    have e : ((BitVec.ofNat 64 (A + B * 2 ^ 31 + C * 2 ^ 47)) <<< 17) >>> 48 = BitVec.ofNat 64 B := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toN, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : B < 2 ^ 64)]
      have : (A + B * 2 ^ 31 + C * 2 ^ 47) * 2 ^ 17 % 2 ^ 64 = (A + B * 2 ^ 31) * 2 ^ 17 := by
        rw [show (2 : Nat) ^ 64 = 2 ^ 47 * 2 ^ 17 by norm_num, Nat.mul_mod_mul_right]
        congr 1; omega
      rw [this]; omega
    rw [e, ← BitVec.ofInt_natCast, s16, osub, eB]; congr 1; ring
  · rw [pextHi, hY]
    have e : (BitVec.ofNat 64 (A + B * 2 ^ 31 + C * 2 ^ 47)) >>> 47 = BitVec.ofNat 64 C := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, toN, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (by omega : C < 2 ^ 64)]
      omega
    rw [e, ← BitVec.ofInt_natCast, s16, osub, eC]; congr 1; ring

/-! ## The low words after a chunk -/

theorem ofInt_toNat64 (w : BitVec 64) : BitVec.ofInt 64 (w.toNat : Int) = w := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A chunk's update of a low word: from words congruent to `F`, `G` modulo
`2^K`, `(fw u + gw v) >> n` (modulo `2^64`) is congruent to `f'` modulo
`2^(K - n)`, for `2^n f' = u F + v G`. -/
theorem low_upd {fw gw : BitVec 64} {F G u v f' : Int} {K n : Nat} (hK : K ≤ 64) (hn : n ≤ K)
    (hf : (fw.toNat : Int) % 2 ^ K = F % 2 ^ K) (hg : (gw.toNat : Int) % 2 ^ K = G % 2 ^ K)
    (h : 2 ^ n * f' = u * F + v * G) :
    ((((fw * BitVec.ofInt 64 u + gw * BitVec.ofInt 64 v) >>> n).toNat : Nat) : Int) % 2 ^ (K - n) =
      f' % 2 ^ (K - n) := by
  have hX : fw * BitVec.ofInt 64 u + gw * BitVec.ofInt 64 v =
      BitVec.ofInt 64 ((fw.toNat : Int) * u + (gw.toNat : Int) * v) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_mul, ofInt_toNat64, ofInt_toNat64]
  rw [hX, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Int.natCast_div]
  have hd : (2 : Int) ^ K ∣ 2 ^ 64 := pow_dvd_pow 2 hK
  have hNK : ((BitVec.ofInt 64 ((fw.toNat : Int) * u + (gw.toNat : Int) * v)).toNat : Int) % 2 ^ K =
      2 ^ n * f' % 2 ^ K := by
    rw [toNat_ofInt64, Int.emod_emod_of_dvd _ hd, h, Int.add_emod, Int.mul_emod, hf, ← Int.mul_emod,
      Int.mul_emod _ v, hg, ← Int.mul_emod, ← Int.add_emod]
    congr 1; ring
  obtain ⟨c, hc⟩ := Int.ModEq.dvd hNK.symm
  have e : ((BitVec.ofInt 64 ((fw.toNat : Int) * u + (gw.toNat : Int) * v)).toNat : Int) =
      2 ^ n * (f' + 2 ^ (K - n) * c) := by
    have : (2 : Int) ^ K = 2 ^ n * 2 ^ (K - n) := by rw [← pow_add]; congr 1; omega
    rw [this] at hc; linear_combination hc
  rw [e, Nat.cast_pow, Nat.cast_ofNat, Int.mul_ediv_cancel_left _ (by positivity), Int.add_mul_emod_self_left]

end VG.Proof.Divstep
