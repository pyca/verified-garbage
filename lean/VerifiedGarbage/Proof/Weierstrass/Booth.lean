import VerifiedGarbage.Proof.Weierstrass.CombW

/-!
# Signed (Booth) digits for the fixed-base comb, and why they never collide

With `w`-bit windows, Booth's recoding writes `k < 2^(wJ - 1)` as
`k = Σ_{j<J} d_j 2^(wj)` with `d_j = W_j + c_j - 2^w c_{j+1}` (`bdig`): `W_j`
the window `j` of `k` (`combWin`) and `c_j` the bit `wj - 1` of `k` (`bcar`,
`c_0 = 0`), so `|d_j| ≤ 2^(w-1)` (`bmag_le`) and the digits need no constant
added. Their partial sums from the bottom, `bpart j = Σ_{i<j} d_i 2^(wi)`
(`bpart_succ`), are `k mod 2^(wj) - c_j 2^(wj)`, so `|bpart j| ≤ 2^(wj - 1)`
(`bpart_abs_le`): smaller than any digit's term above them.

A comb adding the digits from the bottom with a formula that fails for equal
points (Jacobian mixed addition) needs `[bpart j]G ≠ [d_j 2^(wj)]G` for every
nonzero digit (`booth_ne`). That holds when `G` has order `n` (`[n]G = O`, `n`
prime: integer multiples of `G` agree only for integers congruent modulo `n`,
`Law.zmul_dvd`) and the digits' terms are too small to wrap around `n`, which
`BoothSafe` checks of `n`, `w`, `J` and the scalars' bound (decidably).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-! ## Integer multiples -/

/-- `[z]P` for an integer `z`: the reflection of `[-z]P` for `z < 0`. -/
def zmul (z : Int) (P : Point C) : Point C :=
  if 0 ≤ z then mul z.toNat P else negPt (mul (-z).toNat P)

theorem zmul_natCast (k : Nat) (P : Point C) : zmul (k : Int) P = mul k P := by
  simp [zmul]

theorem Law.onCurve_zmul (hC : Law C) {P : Point C} (hP : onCurve C P = true) (z : Int) :
    onCurve C (zmul z P) = true := by
  unfold zmul
  split
  · exact hC.onCurve_mul hP _
  · exact onCurve_negPt (hC.onCurve_mul hP _)

theorem Law.group_zmul (hC : Law C) {A : Type} [Lean.Grind.IntModule A] {f : Point C → A}
    (hf : GroupRep C A f) {P : Point C} (hP : onCurve C P = true) (z : Int) :
    f (zmul z P) = z • f P := by
  unfold zmul
  split
  · rw [hf.mul hP]
    congr 1
    omega
  · rw [hf.neg (hC.onCurve_mul hP _), hf.mul hP, ← Lean.Grind.IntModule.neg_zsmul]
    congr 1
    omega

/-- `[a]P + [b]P = [a + b]P`, for integers. -/
theorem Law.add_zmul (hC : Law C) {P : Point C} (hP : onCurve C P = true) (a b : Int) :
    Spec.Weierstrass.add (zmul a P) (zmul b P) = zmul (a + b) P := by
  obtain ⟨A, _, f, hf⟩ := hC.group
  apply hf.inj (hC.onCurve_add (hC.onCurve_zmul hP a) (hC.onCurve_zmul hP b)) (hC.onCurve_zmul hP _)
  rw [hf.add (hC.onCurve_zmul hP a) (hC.onCurve_zmul hP b), hC.group_zmul hf hP, hC.group_zmul hf hP,
    hC.group_zmul hf hP, Lean.Grind.IntModule.add_zsmul]

/-! ## The order of `G` -/

section
variable {A : Type} [Lean.Grind.IntModule A]

theorem zsmul_mul_eq_zero (g : A) {m : Nat} (hm : (m : Int) • g = 0) :
    ∀ q : Nat, ((q * m : Nat) : Int) • g = 0
  | 0 => by simp [Lean.Grind.IntModule.zero_zsmul]
  | q + 1 => by
    rw [Nat.succ_mul, Int.natCast_add, Lean.Grind.IntModule.add_zsmul, zsmul_mul_eq_zero g hm q, hm]
    grind

/-- What kills `g` is closed under `gcd`. -/
theorem zsmul_gcd_eq_zero (g : A) : ∀ m n : Nat, (m : Int) • g = 0 → (n : Int) • g = 0 →
    ((Nat.gcd m n : Nat) : Int) • g = 0 := by
  intro m n
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; rw [Nat.gcd_zero_left]; exact hn
  | H1 m n hm ih =>
    intro hmg hng
    rw [Nat.gcd_rec]
    refine ih ?_ hmg
    have e := (Nat.div_add_mod' n m).symm
    have h := zsmul_mul_eq_zero g hmg (n / m)
    rw [e, Int.natCast_add, Lean.Grind.IntModule.add_zsmul, h] at hng
    grind
end

/-- The order of `G` is `n`, prime: integer multiples of `G` agree only for
integers congruent modulo `n`. -/
theorem Law.zmul_dvd (hC : Law C) (hG : onCurve C (G C) = true)
    (hn : mul C.n (G C) = .infinity) (hn0 : 0 < C.n)
    (hcop : ∀ m, 0 < m → m < C.n → Nat.gcd m C.n = 1) {a b : Int}
    (h : zmul a (G C) = zmul b (G C)) : (C.n : Int) ∣ a - b := by
  obtain ⟨A, _, f, hf⟩ := hC.group
  have hinf : f .infinity = 0 := by
    have := hf.mul hG 0
    rw [show mul 0 (G C) = .infinity by rw [Spec.Weierstrass.mul]; simp,
      Int.natCast_zero, Lean.Grind.IntModule.zero_zsmul] at this
    exact this
  have hng : (C.n : Int) • f (G C) = 0 := by rw [← hf.mul hG, hn, hinf]
  have hab : (a - b) • f (G C) = 0 := by
    have h' := congrArg f h
    rw [hC.group_zmul hf hG, hC.group_zmul hf hG] at h'
    rw [Int.sub_eq_add_neg, Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.neg_zsmul, h']
    grind
  have habs : ((a - b).natAbs : Int) • f (G C) = 0 := by
    rcases Int.natAbs_eq (a - b) with e | e
    · rw [← e]; exact hab
    · have : ((a - b).natAbs : Int) = -(a - b) := by omega
      rw [this, Lean.Grind.IntModule.neg_zsmul, hab]; grind
  rw [← Int.natAbs_dvd_natAbs]
  simp only [Int.natAbs_natCast]
  refine Classical.byContradiction fun hnd => ?_
  have hm : 0 < (a - b).natAbs % C.n := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hg1 : Nat.gcd ((a - b).natAbs) C.n = 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec]
    exact hcop _ hm (Nat.mod_lt _ hn0)
  have h1 := zsmul_gcd_eq_zero (f (G C)) _ _ habs hng
  rw [hg1, Int.natCast_one, Lean.Grind.IntModule.one_zsmul] at h1
  have := hf.inj (P := G C) (Q := .infinity) hG rfl (h1.trans hinf.symm)
  exact nomatch this

/-! ## Booth's digits -/

theorem two_pow_pred {t : Nat} (ht : 1 ≤ t) : 2 ^ t = 2 * 2 ^ (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  rw [Nat.pow_succ, Nat.add_sub_cancel, Nat.mul_comm]

/-- `c_j`: bit `wj - 1` of `k`, `0` for `j = 0`. -/
def bcar (w k j : Nat) : Nat := if j = 0 then 0 else k / 2 ^ (w * j - 1) % 2

/-- Digit `j`: `W_j + c_j - 2^w c_{j+1}`. -/
def bdig (w k j : Nat) : Int :=
  ((combWin w k j + bcar w k j : Nat) : Int) - ((2 ^ w * bcar w k (j + 1) : Nat) : Int)

/-- The sum of the digits below `j`, each at its place. -/
def bpart (w k j : Nat) : Int :=
  ((k % 2 ^ (w * j) : Nat) : Int) - ((2 ^ (w * j) * bcar w k j : Nat) : Int)

theorem bcar_le (w k j : Nat) : bcar w k j ≤ 1 := by
  unfold bcar; split <;> omega

/-- The bit below a multiple of `2^t`, from the residue. -/
theorem div_pow_mod_two (k t : Nat) : k / 2 ^ t % 2 = k % 2 ^ (t + 1) / 2 ^ t := by
  rw [Nat.pow_succ, Nat.mod_mul_right_div_self]

theorem bpart_zero (w k : Nat) : bpart w k 0 = 0 := by simp [bpart, bcar]

/-- `c_{j+1}` is the top bit of window `j`. -/
theorem bcar_succ {w : Nat} (hw : 1 ≤ w) (k j : Nat) :
    bcar w k (j + 1) = combWin w k j / 2 ^ (w - 1) := by
  have e : w * (j + 1) - 1 = w * j + (w - 1) := by rw [Nat.mul_succ]; omega
  simp only [bcar, Nat.add_one_ne_zero, ↓reduceIte, e, Nat.pow_add, combWin]
  rw [← Nat.div_div_eq_div_mul, div_pow_mod_two, show w - 1 + 1 = w by omega]

/-- `bpart (j + 1) = bpart j + d_j 2^(wj)`. -/
theorem bpart_succ (w k j : Nat) :
    bpart w k (j + 1) = bpart w k j + bdig w k j * ((2 ^ (w * j) : Nat) : Int) := by
  have hpw : 2 ^ (w * (j + 1)) = 2 ^ (w * j) * 2 ^ w := pow_w_succ w j
  have hres : k % 2 ^ (w * (j + 1)) = k % 2 ^ (w * j) + 2 ^ (w * j) * combWin w k j := by
    rw [hpw, Nat.mod_mul]; rfl
  simp only [bpart, bdig]
  rw [hres, hpw]
  push_cast
  grind

/-- The digits add up to `k`. -/
theorem bpart_top {w k J : Nat} (hJ : 1 ≤ J) (hk : k < 2 ^ (w * J - 1)) :
    bpart w k J = k := by
  have hk' : k < 2 ^ (w * J) := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : bcar w k J = 0 := by
    simp only [bcar, show J ≠ 0 by omega, ↓reduceIte, Nat.div_eq_of_lt hk, Nat.zero_mod]
  simp [bpart, hc, Nat.mod_eq_of_lt hk']

/-- `|bpart j| ≤ 2^(wj - 1)`. -/
theorem bpart_abs_le {w : Nat} (hw : 1 ≤ w) (k : Nat) {j : Nat} (hj : 1 ≤ j) :
    (bpart w k j).natAbs ≤ 2 ^ (w * j - 1) := by
  have hwj : 1 ≤ w * j := Nat.mul_le_mul hw hj
  have e := two_pow_pred hwj
  have hc : bcar w k j = k % 2 ^ (w * j) / 2 ^ (w * j - 1) := by
    simp only [bcar, show j ≠ 0 by omega, ↓reduceIte]
    rw [div_pow_mod_two, show w * j - 1 + 1 = w * j by omega]
  have hm := Nat.mod_lt k (Nat.two_pow_pos (w * j))
  have hd := Nat.div_add_mod (k % 2 ^ (w * j)) (2 ^ (w * j - 1))
  have hl := Nat.mod_lt (k % 2 ^ (w * j)) (Nat.two_pow_pos (w * j - 1))
  have hq : k % 2 ^ (w * j) / 2 ^ (w * j - 1) ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)]; omega
  simp only [bpart, hc]
  generalize 2 ^ (w * j - 1) = h at *
  generalize k % 2 ^ (w * j) = r at *
  rw [e]
  rcases (by omega : r / h = 0 ∨ r / h = 1) with h0 | h0 <;> rw [h0] at hd ⊢ <;> omega

/-- The digit's magnitude. -/
def bmag (w k j : Nat) : Nat := (bdig w k j).natAbs

/-- `|d_j| ≤ 2^(w-1)`. -/
theorem bmag_le {w : Nat} (hw : 1 ≤ w) (k j : Nat) : bmag w k j ≤ 2 ^ (w - 1) := by
  have hW := combWin_lt w k j
  have hc := bcar_le w k j
  have h2 := two_pow_pred hw
  have hd := Nat.div_add_mod (combWin w k j) (2 ^ (w - 1))
  have hl := Nat.mod_lt (combWin w k j) (Nat.two_pow_pos (w - 1))
  have hq : combWin w k j / 2 ^ (w - 1) ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)]; omega
  simp only [bmag, bdig, bcar_succ hw]
  rw [h2]
  generalize 2 ^ (w - 1) = h at *
  generalize combWin w k j = W at *
  generalize W / h = q at *
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> omega

/-- The digit's sign and magnitude: for a window whose top bit
`c_{j+1}` is set, `d_j = -(2^w - (W_j + c_j)) ≤ 0`, else `d_j = W_j + c_j ≥ 0`. -/
theorem bdig_cases {w : Nat} (hw : 1 ≤ w) (k j : Nat) :
    (bcar w k (j + 1) = 1 ∧ combWin w k j + bcar w k j ≤ 2 ^ w ∧
        bdig w k j = -((2 ^ w - (combWin w k j + bcar w k j) : Nat) : Int)) ∨
    (bcar w k (j + 1) = 0 ∧ bdig w k j = ((combWin w k j + bcar w k j : Nat) : Int)) := by
  have hW := combWin_lt w k j
  have hc := bcar_le w k j
  have h2 := two_pow_pred hw
  have hd := Nat.div_add_mod (combWin w k j) (2 ^ (w - 1))
  have hl := Nat.mod_lt (combWin w k j) (Nat.two_pow_pos (w - 1))
  have hq : combWin w k j / 2 ^ (w - 1) ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)]; omega
  simp only [bdig, bcar_succ hw]
  rw [h2] at hW ⊢
  generalize 2 ^ (w - 1) = h at *
  generalize combWin w k j = W at *
  generalize W / h = q at *
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> omega

/-- The magnitude the code computes: `s ? 2^w - (W_j + c_j) : W_j + c_j`. -/
theorem bmag_eq {w : Nat} (hw : 1 ≤ w) (k j : Nat) :
    bmag w k j = if bcar w k (j + 1) = 1 then 2 ^ w - (combWin w k j + bcar w k j)
      else combWin w k j + bcar w k j := by
  unfold bmag
  rcases bdig_cases hw k j with ⟨h1, -, h⟩ | ⟨h0, h⟩
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast]; simp only [h1, ↓reduceIte]
  · rw [h, Int.natAbs_natCast]; simp only [h0, Nat.zero_ne_one, ↓reduceIte]

/-- The point of digit `j` at its place: the entry of its magnitude in table
`j`, reflected where the window's top bit is set (a negative digit, or `0`). -/
def bentry (C : Curve) (w k j : Nat) : Point C :=
  if bcar w k (j + 1) = 1 then negPt (combPtW C w j (bmag w k j)) else combPtW C w j (bmag w k j)

theorem bentry_eq {w : Nat} (hw : 1 ≤ w) (k j : Nat) :
    bentry C w k j = zmul (bdig w k j * ((2 ^ (w * j) : Nat) : Int)) (G C) := by
  have hP := Nat.two_pow_pos (w * j)
  unfold bentry zmul combPtW
  rcases bdig_cases hw k j with ⟨h1, -, h⟩ | ⟨h0, h⟩
  · have hm : bmag w k j = 2 ^ w - (combWin w k j + bcar w k j) := by
      unfold bmag; rw [h, Int.natAbs_neg, Int.natAbs_natCast]
    simp only [h1, ↓reduceIte]
    rw [h, ← hm]
    by_cases h0 : bmag w k j = 0
    · rw [h0]
      simp only [Int.natCast_zero, Int.neg_zero, Int.zero_mul, Int.le_refl, ↓reduceIte,
        Int.toNat_zero, Nat.zero_mul]
      rw [show mul 0 (G C) = .infinity by rw [Spec.Weierstrass.mul]; simp]
      rfl
    · have e : -(-((bmag w k j : Nat) : Int) * ((2 ^ (w * j) : Nat) : Int)) =
          ((bmag w k j * 2 ^ (w * j) : Nat) : Int) := by
        rw [Int.neg_mul, Int.neg_neg, Int.natCast_mul]
      have hneg : ¬ (0 ≤ -((bmag w k j : Nat) : Int) * ((2 ^ (w * j) : Nat) : Int)) := by
        rw [Int.neg_mul, ← Int.natCast_mul]
        have : 0 < bmag w k j * 2 ^ (w * j) := Nat.mul_pos (by omega) hP
        omega
      simp only [hneg, ↓reduceIte]
      rw [e, Int.toNat_natCast]
  · have hm : bmag w k j = combWin w k j + bcar w k j := by
      unfold bmag; rw [h, Int.natAbs_natCast]
    simp only [h0, Nat.zero_ne_one, ↓reduceIte]
    rw [h, ← hm, ← Int.natCast_mul]
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]

/-! ## No collisions -/

/-- What the comb needs of `n`, `w`, `J` and the bound `kmax` on its scalars
for its digits' terms never to meet the sum below them modulo `n`: the terms
below the top window, with the sums below them, stay below `n`, and no top
digit `d` (with `e = d 2^(w(J-1))`) and multiple `t n` give a scalar
`2e - tn < kmax` whose sum below the top, `e - tn`, is small enough. -/
def BoothSafe (n w J kmax : Nat) : Prop :=
  (2 ^ (w - 1) + 1) * 2 ^ (w * (J - 2)) < n ∧
  ∀ d < 2 ^ (w - 1) + 1, ∀ t < 2 * (d * 2 ^ (w * (J - 1))) / n + 1,
    ¬ (1 ≤ d ∧ 1 ≤ t ∧ t * n ≤ 2 * (d * 2 ^ (w * (J - 1))) ∧
      2 * (d * 2 ^ (w * (J - 1))) - t * n < kmax ∧
      d * 2 ^ (w * (J - 1)) ≤ t * n + 2 ^ (w * (J - 1) - 1) ∧
      t * n ≤ d * 2 ^ (w * (J - 1)) + 2 ^ (w * (J - 1) - 1))

instance (n w J kmax : Nat) : Decidable (BoothSafe n w J kmax) := by
  unfold BoothSafe; infer_instance

/-- The arithmetic of `booth_ne`: `n` does not divide `P - e` for the sum
`P` below digit `j` and its term `e = d 2^(wj)`, `d ≠ 0`. -/
theorem booth_not_dvd {n w J kmax : Nat} (hsafe : BoothSafe n w J kmax) (hw : 1 ≤ w) (hJ : 2 ≤ J)
    (hkJ : kmax ≤ 2 ^ (w * J - 1)) (hn0 : 0 < n) {k : Nat} (hk : k < kmax) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j < J) (hm : bmag w k j ≠ 0) :
    ¬ (n : Int) ∣ bpart w k j - bdig w k j * ((2 ^ (w * j) : Nat) : Int) := by
  rintro ⟨x, hx⟩
  have hsum := bpart_succ w k j
  have hP := bpart_abs_le hw k hj1
  have hD := bmag_le hw k j
  have hE := two_pow_pred (Nat.mul_le_mul hw hj1)
  have hEpos := Nat.two_pow_pos (w * j)
  obtain ⟨m, hm1, hmH, hdig⟩ : ∃ m : Nat, 1 ≤ m ∧ m ≤ 2 ^ (w - 1) ∧
      (bdig w k j = m ∨ bdig w k j = -(m : Int)) :=
    ⟨bmag w k j, Nat.pos_of_ne_zero hm, hD, by unfold bmag; omega⟩
  have hME : 2 ^ (w * j) ≤ m * 2 ^ (w * j) := Nat.le_mul_of_pos_left _ hm1
  have hMH : m * 2 ^ (w * j) ≤ 2 ^ (w - 1) * 2 ^ (w * j) := Nat.mul_le_mul_right _ hmH
  have he : bdig w k j * ((2 ^ (w * j) : Nat) : Int) = ((m * 2 ^ (w * j) : Nat) : Int) ∨
      bdig w k j * ((2 ^ (w * j) : Nat) : Int) = -((m * 2 ^ (w * j) : Nat) : Int) := by
    rcases hdig with h | h <;> rw [h]
    · exact Or.inl (Int.natCast_mul _ _).symm
    · exact Or.inr (by rw [Int.neg_mul, Int.natCast_mul])
  clear hdig
  have habs : (bpart w k j - bdig w k j * ((2 ^ (w * j) : Nat) : Int)).natAbs = n * x.natAbs := by
    rw [hx, Int.natAbs_mul, Int.natAbs_natCast]
  by_cases htop : j + 1 < J
  · -- Below the top: `0 < |P - e| < n`.
    have hjle : 2 ^ (w * j) ≤ 2 ^ (w * (J - 2)) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
    have h3 : 2 ^ (w - 1) * 2 ^ (w * j) ≤ 2 ^ (w - 1) * 2 ^ (w * (J - 2)) :=
      Nat.mul_le_mul_left _ hjle
    have hs := hsafe.1
    rw [Nat.add_mul, Nat.one_mul] at hs
    generalize 2 ^ (w - 1) * 2 ^ (w * (J - 2)) = HX at h3 hs
    generalize 2 ^ (w - 1) * 2 ^ (w * j) = HE at h3 hMH
    generalize 2 ^ (w * (J - 2)) = X at hjle hs
    generalize m * 2 ^ (w * j) = ME at hME hMH he
    generalize 2 ^ (w * j - 1) = B at hP hE
    generalize 2 ^ (w * j) = E at *
    generalize bdig w k j * (E : Int) = e at he habs
    generalize bpart w k j = P at hP habs
    have hx0 : x.natAbs ≠ 0 := by
      intro h0; rw [h0, Nat.mul_zero] at habs; rcases he with rfl | rfl <;> omega
    have : n * 1 ≤ n * x.natAbs := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hx0)
    generalize n * x.natAbs = NX at habs this
    rcases he with rfl | rfl <;> omega
  · -- The top window: `P + e = k`, so `e > 0`, `P - e = -t n`.
    have hjJ : j + 1 = J := by omega
    rw [hjJ, bpart_top (by omega) (Nat.lt_of_lt_of_le hk hkJ)] at hsum
    have hcheck := hsafe.2 m (by omega)
    rw [show J - 1 = j by omega] at hcheck
    generalize m * 2 ^ (w * j) = ME at hME hMH he hcheck
    generalize 2 ^ (w * j - 1) = B at hP hE hcheck
    generalize 2 ^ (w * j) = E at *
    generalize bdig w k j * (E : Int) = e at he habs hsum hx
    generalize bpart w k j = P at hP habs hsum hx
    have hep : e = (ME : Int) := by rcases he with h | h <;> omega
    subst hep
    -- `n x = P - ME < 0`.
    have hxneg : (n : Int) * x < 0 := by omega
    obtain ⟨t, ht1, rfl⟩ : ∃ t : Nat, 1 ≤ t ∧ x = -(t : Int) := by
      have hx0 : x < 0 := by
        refine Classical.byContradiction fun h => ?_
        have : 0 ≤ (n : Int) * x := Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
        omega
      exact ⟨(-x).toNat, by omega, by omega⟩
    have htn : ((t * n : Nat) : Int) = ME - P := by
      rw [Int.natCast_mul, Int.mul_comm]
      have : (n : Int) * -(t : Int) = -((n : Int) * t) := Int.mul_neg _ _
      omega
    have h2 : t * n ≤ 2 * ME := by omega
    have hlt : t < 2 * ME / n + 1 := by
      have := (Nat.le_div_iff_mul_le hn0).mpr h2; omega
    exact hcheck t hlt ⟨hm1, ht1, h2, by omega, by omega, by omega⟩

/-- The sum below digit `j` is never the digit's term, as a multiple of `G`. -/
theorem booth_ne (hC : Law C) (hG : onCurve C (G C) = true)
    (hn : mul C.n (G C) = .infinity) (hn0 : 0 < C.n)
    (hcop : ∀ m, 0 < m → m < C.n → Nat.gcd m C.n = 1) {w J kmax : Nat}
    (hsafe : BoothSafe C.n w J kmax) (hw : 1 ≤ w) (hJ : 2 ≤ J) (hkJ : kmax ≤ 2 ^ (w * J - 1))
    {k : Nat} (hk : k < kmax) {j : Nat} (hj1 : 1 ≤ j) (hj : j < J) (hm : bmag w k j ≠ 0) :
    zmul (bpart w k j) (G C) ≠ zmul (bdig w k j * ((2 ^ (w * j) : Nat) : Int)) (G C) :=
  fun heq => booth_not_dvd hsafe hw hJ hkJ hn0 hk hj1 hj hm (hC.zmul_dvd hG hn hn0 hcop heq)

/-- What the comb with Booth's digits needs of the curve, for `J ≥ 2` digits
of `w` bits and scalars below `kmax ≤ 2^(wJ - 1)`: `G` of order `n`, whose
multiples below `n` are coprime to it (`n` prime), and `BoothSafe`. -/
structure BoothOk (C : Curve) (w J kmax : Nat) : Prop where
  n : mul C.n (G C) = .infinity
  n0 : 0 < C.n
  cop : ∀ m, 0 < m → m < C.n → Nat.gcd m C.n = 1
  safe : BoothSafe C.n w J kmax
  J2 : 2 ≤ J
  kmax : kmax ≤ 2 ^ (w * J - 1)

end VG.Proof.Weierstrass
