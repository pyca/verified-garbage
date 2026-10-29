module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Mont.X86.Square.RedStage
import VerifiedGarbage.Proof.Mont.X86.Square.InputMath

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont

def qDigits (s : State) (W : Addr) (S i : Nat) : Nat := w32 s.mem W (S+52+4*i)
def mDigits (s : State) (W : Addr) (m i : Nat) : Nat := w32 s.mem W (m+4*i)

theorem red_value (s : State) (W : Addr) (S m : Nat) {N k : Nat} (hk : k<2*N) :
    redLow s W S m N k + 2^32*redHigh s W S m N k =
      Column.coeff (Column.prefixDigits (qDigits s W S) k) (mDigits s W m) N k := by
  unfold redLow redHigh
  rw [total_split, total_eq_sum, Column.coeff_prefix_scan]
  apply NatSum.congr
  intro j hj
  have jb := hj
  unfold dotProd qDigits mDigits
  have e1 : S+52+4*(k+1-N)+4*j = S+52+4*(k+1-N+j) := by omega
  have e2 : m+4*(k-(k+1-N))-4*j = m+4*(k-(k+1-N+j)) := by
    dsimp [redCount] at jb
    omega
  rw [e1, e2]

theorem red_bounds (s : State) (W : Addr) (S m N k : Nat) :
    redLow s W S m N k ≤ N*(2^32-1) ∧ redHigh s W S m N k ≤ N*(2^32-1) := by
  have count : redCount N k≤N := by unfold redCount; omega
  constructor
  · have bound : redLow s W S m N k ≤ redCount N k*(2^32-1) :=
      total_le_const _ (fun j _ => by exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide)))
    exact Nat.le_trans bound (Nat.mul_le_mul_right _ count)
  · have bound : redHigh s W S m N k ≤ redCount N k*(2^32-1) := by
      apply total_le_const
      intro j hj
      have left := (s.mem.readW (off W (S+52+4*(k+1-N)+4*j)) 32).isLt
      have right := (s.mem.readW (off W (m+4*(k-(k+1-N))-4*j)) 32).isLt
      have prod := Nat.mul_lt_mul'' left right
      have lt : dotProd s W (S+52+4*(k+1-N)) (m+4*(k-(k+1-N))) j / 2^32 < 2^32 :=
        (Nat.div_lt_iff_lt_mul (by decide)).2 prod
      exact Nat.le_sub_one_of_lt lt
    exact Nat.le_trans bound (Nat.mul_le_mul_right _ count)

end VG.Proof.Mont.X86.Square
