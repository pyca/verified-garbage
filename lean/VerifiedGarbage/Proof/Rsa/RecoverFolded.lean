module

public import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Proof.RsaKeyGen.MillerRabin

/-! # Recovering a root while exponentiation continues

Unlike the original recovery loop, the exponentiation accumulator must
continue squaring after a root has been found: a later nonzero exponent
digit can invalidate that tentative root. Keep the root separately, and
reset the flags at each nonzero digit.
-/

@[expose] public section

namespace VG.Proof.Rsa.RecoveryFolded

open VG.Spec.Rsa

structure Track where
  root : Nat
  stopped : Bool
  found : Bool
  deriving DecidableEq

def result (s : Track) : Option Nat := if s.found then some s.root else none

def start (n y root : Nat) : Track :=
  ⟨root, decide (y = 1) || decide (y = n - 1), false⟩

/-- The accumulator always advances. Only the captured root stops changing. -/
def square (n y : Nat) (s : Track) : Track :=
  let x := y * y % n
  let hit := !s.stopped && decide (x = 1)
  ⟨if hit then y else s.root,
    s.stopped || decide (x = 1) || decide (x = n - 1), s.found || hit⟩

def run (n : Nat) : Nat → Nat → Track → Track
  | 0, _, s => s
  | k + 1, y, s => run n k (y * y % n) (square n y s)

theorem square_stopped (n y root : Nat) (found : Bool) :
    square n y ⟨root, true, found⟩ = ⟨root, true, found⟩ := by
  simp [square]

theorem run_stopped (n k y root : Nat) (found : Bool) :
    run n k y ⟨root, true, found⟩ = ⟨root, true, found⟩ := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [run, square_stopped, ih]

/-- A live tracker gives exactly the original recursive root search. -/
theorem run_live (n k y root : Nat) :
    result (run n (k + 1) y ⟨root, false, false⟩) = recoverStep.squarings n k y := by
  induction k generalizing y root with
  | zero =>
    simp only [run, square, Bool.not_false, Bool.true_and, Bool.false_or, result,
      recoverStep.squarings]
    by_cases h : y * y % n = 1 <;> simp [h]
  | succ k ih =>
    rw [run]
    by_cases h1 : y * y % n = 1
    · have hs : square n y ⟨root, false, false⟩ = ⟨y, true, true⟩ := by simp [square, h1]
      rw [hs, run_stopped]
      simp [result, recoverStep.squarings, h1]
    · by_cases hm : y * y % n = n - 1
      · have hn2 : n ≠ 2 := by omega
        have hs : square n y ⟨root, false, false⟩ = ⟨root, true, false⟩ := by simp [square, hm, hn2]
        rw [hs, run_stopped]
        simp [result, recoverStep.squarings, hm, hn2]
      · have hs : square n y ⟨root, false, false⟩ = ⟨root, false, false⟩ := by simp [square, h1, hm]
        rw [hs, ih]
        simp [recoverStep.squarings, h1, hm]

/-- The uninterrupted accumulator and the captured root implement recovery. -/
theorem run_result {n t r g : Nat} (ht : 1 ≤ t) (root : Nat) :
    result (run n t (powMod g r n) (start n (powMod g r n) root)) = recoverStep n t r g := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [recoverStep_eq]
  by_cases h : powMod g r n = 1 ∨ powMod g r n = n - 1
  · have hs : start n (powMod g r n) root = ⟨root, true, false⟩ := by
      simp only [start]; congr 1; simpa using h
    rw [hs, run_stopped]
    simp [result, h]
  · have h1 : powMod g r n ≠ 1 := fun hy => h (Or.inl hy)
    have hm : powMod g r n ≠ n - 1 := fun hy => h (Or.inr hy)
    have hs : start n (powMod g r n) root = ⟨root, false, false⟩ := by simp [start, h1, hm]
    rw [hs, run_live]
    simp [h]

open VG.Proof.RsaKeyGen (sqIter_succ' powMod_pow2)

theorem run_add (n a b y : Nat) (s : Track) :
    run n (a + b) y s = run n b (VG.Proof.RsaKeyGen.sqIter n y a) (run n a y s) := by
  induction a generalizing y s with
  | zero => simp only [Nat.zero_add, VG.Proof.RsaKeyGen.sqIter, run]
  | succ a ih =>
    rw [Nat.succ_add, run, ih, sqIter_succ', run]

/-- A window uses its two uninterrupted squares, then resets at a nonzero digit. -/
def window (n g E j : Nat) (s : Track) : Track :=
  let u := run n 2 (powMod g (E / 4 ^ (j + 1)) n) s
  if E / 4 ^ j % 4 = 0 then u else start n (powMod g (E / 4 ^ j) n) u.root

def scan (n g E : Nat) : Nat → Track → Track
  | 0, s => s
  | j + 1, s => scan n g E j (window n g E j s)

theorem div_four_pow (r a j : Nat) (hj : j ≤ a) :
    r * 4 ^ a / 4 ^ j = r * 4 ^ (a - j) := by
  rw [show a = (a - j) + j by omega, Nat.pow_add, ← Nat.mul_assoc,
    Nat.mul_div_cancel _ (Nat.pow_pos (by decide)), Nat.add_sub_cancel]

theorem powMod_four (n g r a : Nat) (hr : 0 < r) :
    powMod g (r * 4 ^ a) n = VG.Proof.RsaKeyGen.sqIter n (powMod g r n) (2 * a) := by
  have h : 4 ^ a = 2 ^ (2 * a) := by rw [Nat.pow_mul]
  rw [h, powMod_pow2 g r n hr]

/-- Zero windows below the lowest nonzero digit extend the root search. -/
theorem scan_low (n g r a j : Nat) (hr : 0 < r) (hj : j ≤ a) (s : Track) :
    scan n g (r * 4 ^ a) j (run n (2 * (a - j)) (powMod g r n) s) =
      run n (2 * a) (powMod g r n) s := by
  induction j with
  | zero => simp only [scan, Nat.sub_zero]
  | succ j ih =>
    have hdiv := div_four_pow r a j (by omega)
    have hzero : r * 4 ^ a / 4 ^ j % 4 = 0 := by
      rw [hdiv, show a - j = (a - j - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ _
    rw [scan, window, ite_eq_left hzero]
    have hp : powMod g (r * 4 ^ a / 4 ^ (j + 1)) n =
        VG.Proof.RsaKeyGen.sqIter n (powMod g r n) (2 * (a - (j + 1))) := by
      rw [div_four_pow r a (j + 1) hj, powMod_four n g r _ hr]
    rw [hp, ← run_add, show 2 * (a - (j + 1)) + 2 = 2 * (a - j) by omega]
    exact ih (by omega)

/-- At the last nonzero window, all earlier tentative roots are discarded. -/
theorem scan_result {n g r a j sigma : Nat} (hr : r % 2 = 1) (hj : a < j)
    (hsigma : 1 ≤ sigma) (s : Track) :
    result (run n sigma (VG.Proof.RsaKeyGen.sqIter n (powMod g r n) (2 * a))
      (scan n g (r * 4 ^ a) j s)) = recoverStep n (2 * a + sigma) r g := by
  have hr0 : 0 < r := by omega
  induction j generalizing s with
  | zero => omega
  | succ j ih =>
    rw [scan]
    by_cases hja : j = a
    · subst j
      have hdiv : r * 4 ^ a / 4 ^ a = r := by
        rw [div_four_pow r a a (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      have hnonzero : r % 4 ≠ 0 := by omega
      have hlow : ∀ u, scan n g (r * 4 ^ a) a u = run n (2 * a) (powMod g r n) u := by
        intro u
        simpa only [Nat.sub_self, Nat.mul_zero, run] using scan_low n g r a a hr0 (Nat.le_refl _) u
      rw [window, hdiv, ite_eq_right hnonzero, hlow]
      rw [← run_add]
      exact run_result (by omega) _
    · exact ih (by omega) _

def sigma (t : Nat) : Nat := 1 + (t - 1) % 2

theorem sigma_bounds (t : Nat) : 1 ≤ sigma t ∧ sigma t ≤ 2 := by unfold sigma; omega

theorem aligned_twos {t : Nat} (ht : 1 ≤ t) : t = 2 * ((t - 1) / 2) + sigma t := by
  unfold sigma
  omega

theorem aligned_exponent {m : Nat} (hm : 0 < m) (ht : 1 ≤ (splitTwos m).1) :
    m / 2 ^ sigma (splitTwos m).1 = (splitTwos m).2 * 4 ^ (((splitTwos m).1 - 1) / 2) := by
  have he := (VG.Proof.Rsa.splitTwos_spec hm).1
  have ht' := aligned_twos ht
  have hp : 2 ^ (splitTwos m).1 =
      2 ^ (2 * (((splitTwos m).1 - 1) / 2)) * 2 ^ sigma (splitTwos m).1 :=
    (congrArg (fun k => 2 ^ k) ht').trans (Nat.pow_add _ _ _)
  calc m / 2 ^ sigma (splitTwos m).1 =
      (2 ^ (splitTwos m).1 * (splitTwos m).2) / 2 ^ sigma (splitTwos m).1 :=
        congrArg (fun x => x / 2 ^ sigma (splitTwos m).1) he
    _ =
      (splitTwos m).2 * (2 ^ (2 * (((splitTwos m).1 - 1) / 2)) * 2 ^ sigma (splitTwos m).1) /
        2 ^ sigma (splitTwos m).1 := by
          rw [hp, Nat.mul_comm]
    _ = (splitTwos m).2 * 4 ^ (((splitTwos m).1 - 1) / 2) := by
      rw [← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.pow_mul]

end VG.Proof.Rsa.RecoveryFolded
