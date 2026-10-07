import VerifiedGarbage.Proof.Bignum.Square

namespace VG.Proof.Bignum.Triangular
open VG.Proof.Bignum.Square

theorem value_head (r : Nat) (f : Nat → Nat) (n : Nat) :
    value r f (n+1)=f 0+r*value r (fun i => f (i+1)) n := by
  induction n with
  | zero => simp only [value,Nat.pow_zero,Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  | succ n ih =>
    rw [value,ih,value,Nat.pow_succ]
    grind

theorem cross_head (r : Nat) (f : Nat → Nat) (n : Nat) :
    cross r f (n+1)=r*f 0*value r (fun i => f (i+1)) n+r*r*cross r (fun i => f (i+1)) n := by
  induction n with
  | zero => simp only [cross,value,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | succ n ih =>
    rw [cross,ih,value_head,value,cross,Nat.pow_succ]
    grind

/-- Row order for the strictly upper triangle of an `(n+1)`-word block. -/
def rows (r : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => f 0*value r (fun i => f (i+1)) (n+1)+r*r*rows r (fun i => f (i+1)) n

theorem rows_cross (r : Nat) (f : Nat → Nat) (n : Nat) : r*rows r f n=cross r f (n+1) := by
  induction n generalizing f with
  | zero => simp only [rows,cross,value,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | succ n ih =>
    rw [rows,cross_head,← ih]
    grind

theorem value_add (r : Nat) (f : Nat → Nat) (m n : Nat) :
    value r f (m+n)=value r f m+r^m*value r (fun i => f (m+i)) n := by
  induction n with
  | zero => simp only [Nat.add_zero,value,Nat.mul_zero]
  | succ n ih =>
    rw [Nat.add_succ,value,ih,value,Nat.pow_add]
    grind

theorem cross_add (r : Nat) (f : Nat → Nat) (m n : Nat) :
    cross r f (m+n)=cross r f m+r^(2*m)*cross r (fun i => f (m+i)) n+
      r^m*value r f m*value r (fun i => f (m+i)) n := by
  induction n with
  | zero => simp only [Nat.add_zero,cross,value,Nat.mul_zero]
  | succ n ih =>
    rw [Nat.add_succ,cross,ih,value_add,cross,value,Nat.pow_add,
      show 2*m=m+m by omega,Nat.pow_add]
    grind

end VG.Proof.Bignum.Triangular
