module

public import VerifiedGarbage.Proof.Mont.NatSum

/-! Polynomial columns for symmetric squaring and Montgomery cancellation.
`partSum` retains columns below `k`; `prefixDigits` exposes only quotient
digits already written, so the machine proof needs no initialized scratch. -/

@[expose] public section
namespace VG.Proof.Mont.Column
open VG.Proof.Mont.NatSum

def value (r : Nat) (a : Nat → Nat) (N : Nat) : Nat := sum (fun i => a i*r^i) N

def partSum (r : Nat) (a b : Nat → Nat) (N k : Nat) : Nat :=
  sum (fun i => sum (fun j => if i+j<k then a i*b j*r^(i+j) else 0) N) N

def coeff (a b : Nat → Nat) (N k : Nat) : Nat :=
  sum (fun i => sum (fun j => if i+j=k then a i*b j else 0) N) N

theorem partSum_zero (r : Nat) (a b : Nat → Nat) (N : Nat) : partSum r a b N 0=0 := by
  simp [partSum]

theorem partSum_succ (r : Nat) (a b : Nat → Nat) (N k : Nat) :
    partSum r a b N (k+1)=partSum r a b N k+coeff a b N k*r^k := by
  unfold partSum coeff
  rw [← mul, ← add]
  apply NatSum.congr
  intro i hi
  rw [← mul, ← add]
  apply NatSum.congr
  intro j hj
  by_cases e : i+j=k
  · simp [e]
  · by_cases lt : i+j<k
    · simp [lt,e,show i+j<k+1 by omega]
    · simp [lt,e,show ¬ i+j<k+1 by omega]

theorem partSum_done (r : Nat) (a b : Nat → Nat) {N k : Nat} (hk : 2*N≤k) :
    partSum r a b N k=value r a N*value r b N := by
  unfold partSum value
  rw [mul_sum]
  apply NatSum.congr
  intro i hi
  apply NatSum.congr
  intro j hj
  rw [ite_eq_left (by omega), Nat.pow_add]
  ac_rfl

theorem coeff_range (a b : Nat → Nat) (N k : Nat) :
    coeff a b N k=sum (fun i => if i≤k ∧ k-i<N then a i*b (k-i) else 0) N := by
  unfold coeff
  apply NatSum.congr
  intro i hi
  by_cases e : i≤k ∧ k-i<N
  · rw [single N (k-i)]
    · simp [e,show i+(k-i)=k by omega]
    · intro j hj hne; exact ite_eq_right (by omega)
    · simp [e.2]
  · rw [ite_eq_right e]
    apply eq_zero
    intro j hj
    exact ite_eq_right (by omega)

/-- One multiplication for each pair strictly above the diagonal. -/
def crossCoeff (a : Nat → Nat) (N k : Nat) : Nat :=
  sum (fun i => sum (fun j => if i<j ∧ i+j=k then a i*a j else 0) N) N

def diagCoeff (a : Nat → Nat) (N k : Nat) : Nat :=
  sum (fun i => if 2*i=k then a i*a i else 0) N

theorem coeff_square (a : Nat → Nat) (N k : Nat) :
    coeff a a N k=2*crossCoeff a N k+diagCoeff a N k := by
  have split (i j : Nat) : (if i+j=k then a i*a j else 0) =
      (if i<j ∧ i+j=k then a i*a j else 0)+
      (if j<i ∧ i+j=k then a i*a j else 0)+
      (if i=j ∧ i+j=k then a i*a j else 0) := by
    by_cases e : i+j=k
    · rcases Nat.lt_trichotomy i j with h | h | h
      · simp [e,h,Nat.ne_of_lt h,Nat.not_lt_of_ge (Nat.le_of_lt h)]
      · subst j; simp [e]
      · simp [e,h,Ne.symm (Nat.ne_of_lt h),Nat.not_lt_of_ge (Nat.le_of_lt h)]
    · simp [e]
  have swap : sum (fun i => sum (fun j => if j<i ∧ i+j=k then a i*a j else 0) N) N=crossCoeff a N k := by
    rw [comm]
    unfold crossCoeff
    apply NatSum.congr
    intro i hi
    apply NatSum.congr
    intro j hj
    simp only [Nat.add_comm j i,Nat.mul_comm (a j) (a i)]
  have diag : sum (fun i => sum (fun j => if i=j ∧ i+j=k then a i*a j else 0) N) N=diagCoeff a N k := by
    unfold diagCoeff
    apply NatSum.congr
    intro i hi
    rw [single N i]
    · simp [Nat.two_mul]
    · intro j hj hne; simp [Ne.symm hne]
    · exact fun hn => (hn hi).elim
  unfold coeff
  simp only [split,add]
  rw [swap,diag]
  unfold crossCoeff
  omega

theorem diagCoeff_value (a : Nat → Nat) (N k : Nat) :
    diagCoeff a N k=if k%2=0 ∧ k/2<N then a (k/2)*a (k/2) else 0 := by
  unfold diagCoeff
  by_cases e : k%2=0 ∧ k/2<N
  · rw [ite_eq_left e,single N (k/2)]
    · simp [show 2*(k/2)=k by omega]
    · intro j hj hne; exact ite_eq_right (by omega)
    · simp [e.2]
  · rw [ite_eq_right e]
    apply eq_zero
    intro i hi
    exact ite_eq_right (by omega)

theorem crossCoeff_range (a : Nat → Nat) (N k : Nat) :
    crossCoeff a N k=sum (fun i => if i≤k ∧ k-i<N ∧ i<k-i then a i*a (k-i) else 0) N := by
  unfold crossCoeff
  apply NatSum.congr
  intro i hi
  by_cases e : i≤k ∧ k-i<N ∧ i<k-i
  · rw [single N (k-i)]
    · simp [e,show i+(k-i)=k by omega]
    · intro j hj hne; exact ite_eq_right (by omega)
    · simp [e.2.1]
  · rw [ite_eq_right e]
    apply eq_zero
    intro j hj
    exact ite_eq_right (by omega)

theorem crossCoeff_scan (a : Nat → Nat) {N k : Nat} (hk : k<2*N) :
    crossCoeff a N k=sum (fun j => a (k+1-N+j)*a (k-(k+1-N+j))) ((k+1)/2-(k+1-N)) := by
  rw [crossCoeff_range, ← interval (fun i => a i*a (k-i)) N (k+1-N) ((k+1)/2) (by omega)]
  apply NatSum.congr
  intro i hi
  have e : (i≤k ∧ k-i<N ∧ i<k-i) ↔ (k+1-N≤i ∧ i<(k+1)/2) := by omega
  simp only [e]

theorem coeff_bound {a b : Nat → Nat} {N k B : Nat}
    (ha : ∀ i<N, a i≤B) (hb : ∀ i<N, b i≤B) : coeff a b N k≤N*B*B := by
  rw [coeff_range]
  calc sum (fun i => if i≤k ∧ k-i<N then a i*b (k-i) else 0) N ≤ sum (fun _ => B*B) N := by
         apply le
         intro i hi
         split
         · next h => exact Nat.mul_le_mul (ha i hi) (hb (k-i) h.2)
         · exact Nat.zero_le _
       _ = N*B*B := by rw [const,Nat.mul_assoc]

def prefixDigits (q : Nat → Nat) (k i : Nat) : Nat := if i<k then q i else 0

theorem coeff_prefix_scan (q m : Nat → Nat) (N k : Nat) :
    coeff (prefixDigits q k) m N k=sum (fun j => q (k+1-N+j)*m (k-(k+1-N+j))) (min k N-(k+1-N)) := by
  rw [coeff_range, ← interval (fun i => q i*m (k-i)) N (k+1-N) (min k N) (Nat.min_le_right _ _)]
  apply NatSum.congr
  intro i hi
  unfold prefixDigits
  by_cases lt : i<k
  · rw [ite_eq_left lt]
    have e : (i≤k ∧ k-i<N) ↔ (k+1-N≤i ∧ i<min k N) := by omega
    simp only [e]
  · rw [ite_eq_right lt, Nat.zero_mul, ite_self, ite_eq_right (by omega)]

theorem partSum_prefix_succ (r : Nat) (q m : Nat → Nat) (N k : Nat) :
    partSum r (prefixDigits q (k+1)) m N (k+1)=partSum r (prefixDigits q k) m N (k+1)+
      if k<N then q k*m 0*r^k else 0 := by
  have cell (i j : Nat) : (if i+j<k+1 then prefixDigits q (k+1) i*m j*r^(i+j) else 0) =
      (if i+j<k+1 then prefixDigits q k i*m j*r^(i+j) else 0)+
      (if i=k ∧ j=0 then q k*m 0*r^k else 0) := by
    unfold prefixDigits
    by_cases ie : i=k
    · subst i
      by_cases je : j=0
      · subst j; simp
      · have bound : ¬ k+j<k+1 := by omega
        simp [je,bound]
    · by_cases il : i<k
      · simp [ie,il,show i<k+1 by omega]
      · have bound : ¬ i+j<k+1 := by omega
        simp [ie,bound]
  unfold partSum
  simp only [cell,add]
  congr 1
  by_cases hk : k<N
  · rw [ite_eq_left hk,single N k]
    · rw [single N 0]
      · simp
      · intro j hj hne; simp [hne]
      · simp [show 0<N by omega]
    · intro i hi hne; simp [hne]
    · simp [hk]
  · rw [ite_eq_right hk]
    apply eq_zero
    intro i hi
    have ne : i≠k := by omega
    simp [ne]

theorem partSum_congr_left (r : Nat) {a b : Nat → Nat} (m : Nat → Nat) (N k : Nat)
    (h : ∀ i<N, a i=b i) : partSum r a m N k=partSum r b m N k := by
  unfold partSum
  apply NatSum.congr
  intro i hi
  rw [h i hi]

theorem qPart_step (r : Nat) (old new m : Nat → Nat) (N k q : Nat)
    (pref : ∀ i<N, i<k → new i=old i) (digit : k<N → new k=q) (zero : N≤k → q=0) :
    partSum r (prefixDigits new (k+1)) m N (k+1)=partSum r (prefixDigits old k) m N k+
      (coeff (prefixDigits old k) m N k+q*m 0)*r^k := by
  have same : partSum r (prefixDigits new k) m N (k+1)=partSum r (prefixDigits old k) m N (k+1) := by
    apply partSum_congr_left
    intro i hi
    unfold prefixDigits
    split
    · next lt => exact pref i hi lt
    · rfl
  rw [partSum_prefix_succ,same,partSum_succ]
  by_cases hk : k<N
  · rw [ite_eq_left hk,digit hk,Nat.add_mul,Nat.add_assoc]
  · rw [ite_eq_right hk,zero (by omega),Nat.zero_mul,Nat.add_zero,Nat.add_zero]

end VG.Proof.Mont.Column
