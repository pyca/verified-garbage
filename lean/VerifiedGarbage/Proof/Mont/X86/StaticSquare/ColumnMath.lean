module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.ReductionProducts
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.InputProducts
import VerifiedGarbage.Proof.Mont.X86.Square.ColumnMath
public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Mont.Words32
import Mathlib.Util.CompileInductive

/-! # Bounds and cancellation for a complete scalar column -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont

def inputCoeff (mem : Mem) (W : Addr) (a N k : Nat) :=
 Column.coeff (fun i => w32 mem W (a+4*i)) (fun i => w32 mem W (a+4*i)) N k

def redCoeff (mem : Mem) (W : Addr) (S m N k : Nat) :=
 Column.coeff (Column.prefixDigits (fun i => w32 mem W (S+52+4*i)) k)
   (fun i => w32 mem W (m+4*i)) N k

def pre (mem : Mem) (W : Addr) (a S m N k c : Nat) :=
 c+inputCoeff mem W a N k+redCoeff mem W S m N k

def quot (mem : Mem) (W : Addr) (a S m N k c : Nat) :=
 if k<N then (pre mem W a S m N k c%2^32*w32 mem W (S+16))%2^32 else 0

def total (mem : Mem) (W : Addr) (a S m N k c : Nat) :=
 pre mem W a S m N k c+quot mem W a S m N k c*w32 mem W m

 theorem quot_lt (mem : Mem) (W : Addr) (a S m N k c : Nat) : quot mem W a S m N k c<2^32 := by
  unfold quot
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

 theorem column_bounds (mem : Mem) (W : Addr) (a S m : Nat) {N k c : Nat}
    (np : 0<N) (nl : N≤128) (cb : c≤4*N*2^32) :
    total mem W a S m N k c<2^96 ∧ total mem W a S m N k c/2^32≤4*N*2^32 := by
  have word (x : Nat) : w32 mem W x≤2^32-1 := by have := (mem.readW (off W x) 32).isLt; dsimp only [w32]; omega
  have ib : inputCoeff mem W a N k≤N*(2^32-1)*(2^32-1) :=
    Column.coeff_bound (fun i _ => word _) (fun i _ => word _)
  have rb : redCoeff mem W S m N k≤N*(2^32-1)*(2^32-1) := by
    apply Column.coeff_bound _ (fun i _ => word _)
    intro i hi
    unfold Column.prefixDigits
    split
    · exact word _
    · omega
  have qb : quot mem W a S m N k c≤2^32-1 := by have := quot_lt mem W a S m N k c; omega
  have mul := Nat.mul_le_mul qb (word m)
  unfold total pre
  constructor <;> omega

 theorem total_cancel (mem : Mem) (W : Addr) (a S m N k c : Nat) (small : k<N)
    (inverse : (w32 mem W m*w32 mem W (S+16)+1)%2^32=0) :
    total mem W a S m N k c%2^32=0 := by
  unfold total quot
  rw [ite_eq_left small]
  exact Square.cancel_digit _ _ _ _ inverse

 theorem pre_bounds (mem : Mem) (W : Addr) (a S m N k c : Nat)
    (bound : total mem W a S m N k c<2^96) :
    pre mem W a S m N k c<2^96 ∧ inputCoeff mem W a N k<2^96 := by
  unfold total pre at bound
  unfold pre
  omega

end VG.Proof.Mont.X86.StaticSquare
