module

public import VerifiedGarbage.Proof.Framework.Omega

/-! Natural-number sums used by the column-square proof. Keeping these recursive
avoids importing general algebra into every runtime-width RSA caller. -/

@[expose] public section
namespace VG.Proof.Mont.NatSum

def sum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sum f n + f n

@[simp] theorem zero (f : Nat → Nat) : sum f 0 = 0 := rfl
@[simp] theorem succ (f : Nat → Nat) (n : Nat) : sum f (n+1) = sum f n + f n := rfl
@[simp] theorem sum_zero (n : Nat) : sum (fun _ => 0) n = 0 := by
  induction n <;> simp_all [sum]
@[simp] theorem const (c n : Nat) : sum (fun _ => c) n = n*c := by
  induction n <;> simp_all [sum, Nat.succ_mul]

theorem congr {f g : Nat → Nat} {n : Nat} (h : ∀ i<n, f i=g i) : sum f n=sum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ, succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem eq_zero {f : Nat → Nat} {n : Nat} (h : ∀ i<n, f i=0) : sum f n=0 := by
  rw [congr h, sum_zero]

theorem add (f g : Nat → Nat) (n : Nat) : sum (fun i => f i+g i) n=sum f n+sum g n := by
  induction n <;> simp_all [sum] <;> omega

theorem mul (f : Nat → Nat) (n c : Nat) : sum (fun i => f i*c) n=sum f n*c := by
  induction n <;> simp_all [sum, Nat.add_mul]

theorem mul_left (f : Nat → Nat) (n c : Nat) : sum (fun i => c*f i) n=c*sum f n := by
  simpa only [Nat.mul_comm] using mul f n c

theorem le {f g : Nat → Nat} {n : Nat} (h : ∀ i<n, f i≤g i) : sum f n≤sum g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem single {f : Nat → Nat} (n k : Nat)
    (h : ∀ i<n, i≠k → f i=0) (outside : ¬ k<n → f k=0) : sum f n=f k := by
  induction n with
  | zero => simpa using (outside (by omega)).symm
  | succ n ih =>
    by_cases e : n=k
    · subst k
      rw [succ, eq_zero (fun i hi => h i (by omega) (by omega)), Nat.zero_add]
    · rw [succ, h n (by omega) e, Nat.add_zero]
      exact ih (fun i hi => h i (by omega)) (fun hn => outside (by omega))

theorem comm (f : Nat → Nat → Nat) (n m : Nat) :
    sum (fun i => sum (f i) m) n=sum (fun j => sum (fun i => f i j) n) m := by
  induction n with
  | zero => simp
  | succ n ih => simp only [succ, ih, add]

theorem mul_sum (f g : Nat → Nat) (n m : Nat) :
    sum f n*sum g m=sum (fun i => sum (fun j => f i*g j) m) n := by
  simp only [mul_left, mul]

theorem append (f : Nat → Nat) (l d : Nat) :
    sum f (l+d)=sum f l+sum (fun j => f (l+j)) d := by
  induction d with
  | zero => simp
  | succ d ih => simp only [Nat.add_succ, succ, ih]; omega

theorem truncate {f : Nat → Nat} {u n : Nat} (hu : u≤n)
    (h : ∀ i, u≤i → i<n → f i=0) : sum f n=sum f u := by
  rw [show n=u+(n-u) by omega, append]
  rw [eq_zero (fun i hi => h (u+i) (by omega) (by omega)), Nat.add_zero]

theorem interval (f : Nat → Nat) (n l u : Nat) (hu : u≤n) :
    sum (fun i => if l≤i ∧ i<u then f i else 0) n=sum (fun j => f (l+j)) (u-l) := by
  rw [truncate hu (fun i hi _ => ite_eq_right (by omega))]
  by_cases hl : l≤u
  · rw [show u=l+(u-l) by omega, append, Nat.add_sub_cancel_left]
    rw [eq_zero (fun i hi => ite_eq_right (by omega)), Nat.zero_add]
    apply congr
    intro i hi
    exact ite_eq_left (by omega)
  · rw [eq_zero (fun i hi => ite_eq_right (by omega)), show u-l=0 by omega, zero]

end VG.Proof.Mont.NatSum
