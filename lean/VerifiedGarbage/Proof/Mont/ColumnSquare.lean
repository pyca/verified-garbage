module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.Mont.Column
open Finset

def value (r : Nat) (a : Nat → Nat) (N : Nat) : Nat := ∑ i ∈ range N, a i * r ^ i

def partSum (r : Nat) (a b : Nat → Nat) (N k : Nat) : Nat :=
  ∑ i ∈ range N, ∑ j ∈ range N, if i + j < k then a i * b j * r ^ (i+j) else 0

def coeff (a b : Nat → Nat) (N k : Nat) : Nat :=
  ∑ i ∈ range N, ∑ j ∈ range N, if i+j = k then a i * b j else 0

theorem partSum_zero (r : Nat) (a b : Nat → Nat) (N : Nat) : partSum r a b N 0 = 0 := by
  simp [partSum]

theorem partSum_succ (r : Nat) (a b : Nat → Nat) (N k : Nat) :
    partSum r a b N (k+1) = partSum r a b N k + coeff a b N k * r ^ k := by
  unfold partSum coeff
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases e : i+j = k
  · simp [e]
  · by_cases lt : i+j < k
    · simp [lt, e, show i+j < k+1 by omega]
    · simp [lt, e, show ¬ i+j < k+1 by omega]

theorem partSum_done (r : Nat) (a b : Nat → Nat) {N k : Nat} (hk : 2*N ≤ k) :
    partSum r a b N k = value r a N * value r b N := by
  unfold partSum value
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (by have := Finset.mem_range.mp hi; have := Finset.mem_range.mp hj; omega), pow_add]
  ring

theorem coeff_range (a b : Nat → Nat) (N k : Nat) :
    coeff a b N k = ∑ i ∈ range N, if i ≤ k ∧ k-i < N then a i * b (k-i) else 0 := by
  unfold coeff
  apply Finset.sum_congr rfl
  intro i hi
  by_cases e : i ≤ k ∧ k-i < N
  · rw [Finset.sum_eq_single (k-i)]
    · simp [e, show i + (k-i) = k by omega]
    · intro j hj hne
      simp [show i+j ≠ k by omega]
    · simp [Finset.mem_range, e.2]
  · rw [ite_eq_right e]
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]

/-- One multiplication for each pair strictly above the diagonal. -/
def crossCoeff (a : Nat → Nat) (N k : Nat) : Nat :=
  ∑ i ∈ range N, ∑ j ∈ range N, if i < j ∧ i+j = k then a i * a j else 0

def diagCoeff (a : Nat → Nat) (N k : Nat) : Nat :=
  ∑ i ∈ range N, if 2*i = k then a i * a i else 0

theorem coeff_square (a : Nat → Nat) (N k : Nat) :
    coeff a a N k = 2 * crossCoeff a N k + diagCoeff a N k := by
  have split (i j : Nat) :
      (if i+j=k then a i*a j else 0) =
      (if i<j ∧ i+j=k then a i*a j else 0) +
      (if j<i ∧ i+j=k then a i*a j else 0) +
      (if i=j ∧ i+j=k then a i*a j else 0) := by
    by_cases e : i+j=k
    · rcases lt_trichotomy i j with h | h | h
      · simp [e, h, Nat.ne_of_lt h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
      · subst j; simp [e]
      · simp [e, h, Ne.symm (Nat.ne_of_lt h), Nat.not_lt_of_ge (Nat.le_of_lt h)]
    · simp [e]
  have swap : (∑ i ∈ range N, ∑ j ∈ range N, if j<i ∧ i+j=k then a i*a j else 0) = crossCoeff a N k := by
    rw [Finset.sum_comm]
    unfold crossCoeff
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.add_comm j i, Nat.mul_comm (a j) (a i)]
  have diag : (∑ i ∈ range N, ∑ j ∈ range N, if i=j ∧ i+j=k then a i*a j else 0) = diagCoeff a N k := by
    unfold diagCoeff
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [two_mul]
    · intro j hj hne
      simp [Ne.symm hne]
    · exact fun hn => (hn hi).elim
  unfold coeff
  simp_rw [split, Finset.sum_add_distrib]
  rw [swap, diag]
  unfold crossCoeff
  omega

theorem diagCoeff_value (a : Nat → Nat) (N k : Nat) :
    diagCoeff a N k = if k%2 = 0 ∧ k/2 < N then a (k/2)*a (k/2) else 0 := by
  unfold diagCoeff
  by_cases e : k%2=0 ∧ k/2<N
  · rw [ite_eq_left e, Finset.sum_eq_single (k/2)]
    · simp [show 2*(k/2)=k by omega]
    · intro j hj hne
      rw [ite_eq_right (by omega)]
    · simp [Finset.mem_range, e.2]
  · rw [ite_eq_right e]
    apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right (by have := Finset.mem_range.mp hi; omega)]

theorem crossCoeff_range (a : Nat → Nat) (N k : Nat) :
    crossCoeff a N k = ∑ i ∈ range N,
      if i ≤ k ∧ k-i < N ∧ i < k-i then a i * a (k-i) else 0 := by
  unfold crossCoeff
  apply Finset.sum_congr rfl
  intro i hi
  by_cases e : i ≤ k ∧ k-i<N ∧ i<k-i
  · rw [Finset.sum_eq_single (k-i)]
    · simp [e, show i+(k-i)=k by omega]
    · intro j hj hne
      rw [ite_eq_right (by omega)]
    · simp [Finset.mem_range, e.2.1]
  · rw [ite_eq_right e]
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]

theorem crossCoeff_interval (a : Nat → Nat) {N k : Nat} (hk : k<2*N) :
    crossCoeff a N k = ∑ i ∈ Ico (k+1-N) ((k+1)/2), a i*a (k-i) := by
  rw [crossCoeff_range, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem crossCoeff_scan (a : Nat → Nat) {N k : Nat} (hk : k<2*N) :
    crossCoeff a N k = ∑ j ∈ range ((k+1)/2-(k+1-N)),
      a (k+1-N+j)*a (k-(k+1-N+j)) := by
  rw [crossCoeff_interval a hk, Finset.sum_Ico_eq_sum_range]

theorem coeff_bound {a b : Nat → Nat} {N k B : Nat}
    (ha : ∀ i<N, a i ≤ B) (hb : ∀ i<N, b i ≤ B) :
    coeff a b N k ≤ N*B*B := by
  rw [coeff_range]
  calc (∑ i ∈ range N, if i≤k ∧ k-i<N then a i*b (k-i) else 0) ≤ ∑ _i ∈ range N, B*B := by
         apply Finset.sum_le_sum
         intro i hi
         split_ifs with h
         · exact Nat.mul_le_mul (ha i (Finset.mem_range.mp hi)) (hb (k-i) h.2)
         · omega
       _ = N*B*B := by simp [Nat.mul_assoc]

def prefixDigits (q : Nat → Nat) (k i : Nat) : Nat := if i<k then q i else 0

theorem coeff_prefix_scan (q m : Nat → Nat) (N k : Nat) :
    coeff (prefixDigits q k) m N k = ∑ j ∈ range (min k N-(k+1-N)),
      q (k+1-N+j)*m (k-(k+1-N+j)) := by
  rw [coeff_range]
  have e : (∑ i ∈ range N, if i≤k ∧ k-i<N then prefixDigits q k i*m (k-i) else 0) =
      ∑ i ∈ range N, if k+1-N≤i ∧ i<min k N then q i*m (k-i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn := Finset.mem_range.mp hi
    unfold prefixDigits
    split_ifs <;> simp_all <;> omega
  rw [e, ← Finset.sum_filter]
  have sets : (range N).filter (fun i => k+1-N≤i ∧ i<min k N) = Ico (k+1-N) (min k N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [sets, Finset.sum_Ico_eq_sum_range]

theorem partSum_prefix_succ (r : Nat) (q m : Nat → Nat) (N k : Nat) :
    partSum r (prefixDigits q (k+1)) m N (k+1) = partSum r (prefixDigits q k) m N (k+1) +
      if k<N then q k*m 0*r^k else 0 := by
  have cell (i j : Nat) :
      (if i+j<k+1 then prefixDigits q (k+1) i*m j*r^(i+j) else 0) =
      (if i+j<k+1 then prefixDigits q k i*m j*r^(i+j) else 0) +
      (if i=k ∧ j=0 then q k*m 0*r^k else 0) := by
    unfold prefixDigits
    by_cases ie : i=k
    · subst i
      by_cases je : j=0
      · subst j; simp
      · have bound : ¬ k+j<k+1 := by omega
        simp [je, bound]
    · by_cases il : i<k
      · simp [ie, il, show i<k+1 by omega]
      · have bound : ¬ i+j<k+1 := by omega
        simp [ie, bound]
  unfold partSum
  simp_rw [cell, Finset.sum_add_distrib]
  congr 1
  by_cases hk : k<N
  · rw [ite_eq_left hk, Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hne; simp [hne]
      · simp [Finset.mem_range, show 0<N by omega]
    · intro i hi hne; simp [hne]
    · simp [Finset.mem_range, hk]
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i hi
    have ne : i≠k := by have := Finset.mem_range.mp hi; omega
    simp [ne]

theorem partSum_congr_left (r : Nat) {a b : Nat → Nat} (m : Nat → Nat) (N k : Nat)
    (h : ∀ i<N, a i=b i) : partSum r a m N k = partSum r b m N k := by
  unfold partSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem qPart_step (r : Nat) (old new m : Nat → Nat) (N k q : Nat)
    (pref : ∀ i<N, i<k → new i=old i)
    (digit : k<N → new k=q) (zero : N≤k → q=0) :
    partSum r (prefixDigits new (k+1)) m N (k+1) = partSum r (prefixDigits old k) m N k +
      (coeff (prefixDigits old k) m N k+q*m 0)*r^k := by
  have same : partSum r (prefixDigits new k) m N (k+1) = partSum r (prefixDigits old k) m N (k+1) := by
    apply partSum_congr_left
    intro i hi
    unfold prefixDigits
    split_ifs with lt
    · exact pref i hi lt
    · rfl
  rw [partSum_prefix_succ, same, partSum_succ]
  by_cases hk : k<N
  · rw [ite_eq_left hk, digit hk]
    ring
  · rw [ite_eq_right hk, zero (by omega)]
    ring

end VG.Proof.Mont.Column
