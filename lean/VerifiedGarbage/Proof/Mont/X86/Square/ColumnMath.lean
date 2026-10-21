module

public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Mont.X86.Square.RedMath
import VerifiedGarbage.Proof.Mont.X86.Square.Reduction
public import VerifiedGarbage.Proof.Mont.X86.Square.RedStage
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Square.CrossBody
import VerifiedGarbage.Proof.Mont.X86.Square.InputMath

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont

def preLow (s : State) (W : Addr) (a S m N k c : Nat) : Nat :=
  inputLow s W a N k+c%2^32+redLow s W S m N k
def preHigh (s : State) (W : Addr) (a S m N k c : Nat) : Nat :=
  inputHigh s W a N k+c/2^32+redHigh s W S m N k
def nextQ (s : State) (W : Addr) (a S m inv N k c : Nat) : Nat :=
  if k<N then ((preLow s W a S m N k c%2^32)*w32 s.mem W inv)%2^32 else 0
def sumLow (s : State) (W : Addr) (a S m inv N k c : Nat) : Nat :=
  preLow s W a S m N k c+(nextQ s W a S m inv N k c*w32 s.mem W m)%2^32
def sumHigh (s : State) (W : Addr) (a S m inv N k c : Nat) : Nat :=
  preHigh s W a S m N k c+(nextQ s W a S m inv N k c*w32 s.mem W m)/2^32
def nextCarry (s : State) (W : Addr) (a S m inv N k c : Nat) : Nat :=
  sumLow s W a S m inv N k c/2^32+sumHigh s W a S m inv N k c

theorem nextQ_lt (s : State) (W : Addr) (a S m inv N k c : Nat) : nextQ s W a S m inv N k c<2^32 := by
  unfold nextQ
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

theorem column_bounds (s : State) (W : Addr) (a S m inv : Nat) {N k c : Nat}
    (hk : k<2*N) (h8 : 8*N<2^32) (hc : c≤4*N*2^32) :
    sumLow s W a S m inv N k c<2^64 ∧ sumHigh s W a S m inv N k c<2^64 ∧
    nextCarry s W a S m inv N k c≤4*N*2^32 ∧ c<2^64 := by
  have ib := input_bounds s W a hk
  have rb := red_bounds s W S m N k
  have cm : c%2^32≤2^32-1 := by have := Nat.mod_lt c (by decide : 0<2^32); omega
  have cd : c/2^32≤4*N := by omega
  have pm : (nextQ s W a S m inv N k c*w32 s.mem W m)%2^32≤2^32-1 := by
    have := Nat.mod_lt (nextQ s W a S m inv N k c*w32 s.mem W m) (by decide : 0<2^32); omega
  have pd : (nextQ s W a S m inv N k c*w32 s.mem W m)/2^32≤2^32-1 := by
    have q := nextQ_lt s W a S m inv N k c
    have word := (s.mem.readW (off W m) 32).isLt
    have prod := Nat.mul_lt_mul'' q word
    have lt : (nextQ s W a S m inv N k c*w32 s.mem W m)/2^32<2^32 :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 prod
    omega
  have ld : sumLow s W a S m inv N k c/2^32≤2*N+1 := by unfold sumLow preLow; omega
  unfold nextCarry sumLow sumHigh preLow preHigh at *
  omega

theorem column_value (s : State) (W : Addr) (a S m inv : Nat) {N k c : Nat} (hk : k<2*N) :
    sumLow s W a S m inv N k c+2^32*sumHigh s W a S m inv N k c =
      Column.coeff (fun i => w32 s.mem W (a+4*i)) (fun i => w32 s.mem W (a+4*i)) N k +
      Column.coeff (Column.prefixDigits (qDigits s W S) k) (mDigits s W m) N k +
      nextQ s W a S m inv N k c*w32 s.mem W m+c := by
  have ip := input_value s W a hk
  have rp := red_value s W S m hk
  have carry := Nat.mod_add_div c (2^32)
  have product := Nat.mod_add_div (nextQ s W a S m inv N k c*w32 s.mem W m) (2^32)
  unfold sumLow sumHigh preLow preHigh
  simp only [Nat.mul_add]
  omega

theorem nextCarry_value (s : State) (W : Addr) (a S m inv N k c : Nat) :
    sumLow s W a S m inv N k c%2^32+2^32*nextCarry s W a S m inv N k c =
      sumLow s W a S m inv N k c+2^32*sumHigh s W a S m inv N k c := by
  have e := Nat.mod_add_div (sumLow s W a S m inv N k c) (2^32)
  unfold nextCarry
  simp only [Nat.mul_add]
  omega

theorem cancel_digit (r x m i : Nat) (hi : (m*i+1)%r=0) :
    (x+((x%r*i)%r)*m)%r=0 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.add_mod_mod]
  have e : x%r+(x%r*i)*m=(x%r)*(m*i+1) := by grind
  rw [e, Nat.mul_mod, hi, Nat.mul_zero, Nat.zero_mod]

theorem sumLow_zero (s : State) (W : Addr) (a S m inv N k c : Nat) (hk : k<N)
    (hinv : (w32 s.mem W m*w32 s.mem W inv+1)%2^32=0) :
    sumLow s W a S m inv N k c%2^32=0 := by
  unfold sumLow nextQ
  rw [ite_eq_left hk, Nat.add_mod_mod]
  exact cancel_digit _ _ _ _ hinv

end VG.Proof.Mont.X86.Square
