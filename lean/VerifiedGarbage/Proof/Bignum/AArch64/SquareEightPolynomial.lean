module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightColumns
public import VerifiedGarbage.Proof.Bignum.Square
import Mathlib.Tactic.SplitIfs

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64.SquareEight

def columnPolynomial (r : Nat) (f : Nat → Nat) : Nat :=
  r ^ 1 * (f 0 * f 1) +
  r ^ 2 * (f 0 * f 2) +
  r ^ 3 * (f 0 * f 3 + f 1 * f 2) +
  r ^ 4 * (f 0 * f 4 + f 1 * f 3) +
  r ^ 5 * (f 0 * f 5 + f 1 * f 4 + f 2 * f 3) +
  r ^ 6 * (f 0 * f 6 + f 1 * f 5 + f 2 * f 4) +
  r ^ 7 * (f 0 * f 7 + f 1 * f 6 + f 2 * f 5 + f 3 * f 4) +
  r ^ 8 * (f 1 * f 7 + f 2 * f 6 + f 3 * f 5) +
  r ^ 9 * (f 2 * f 7 + f 3 * f 6 + f 4 * f 5) +
  r ^ 10 * (f 3 * f 7 + f 4 * f 6) +
  r ^ 11 * (f 4 * f 7 + f 5 * f 6) +
  r ^ 12 * (f 5 * f 7) +
  r ^ 13 * (f 6 * f 7)

theorem columnPolynomial_cross (r : Nat) (f : Nat → Nat) :
    columnPolynomial r f = Square.cross r f 8 := by
  simp only [columnPolynomial, Square.cross, Square.value, Nat.pow_zero, Nat.mul_one,
    Nat.zero_mul, Nat.zero_add]
  grind

private theorem pairs_1 : pairs 1 = [(0, 1)] := rfl
private theorem pairs_2 : pairs 2 = [(0, 2)] := rfl
private theorem pairs_3 : pairs 3 = [(0, 3), (1, 2)] := rfl
private theorem pairs_4 : pairs 4 = [(0, 4), (1, 3)] := rfl
private theorem pairs_5 : pairs 5 = [(0, 5), (1, 4), (2, 3)] := rfl
private theorem pairs_6 : pairs 6 = [(0, 6), (1, 5), (2, 4)] := rfl
private theorem pairs_7 : pairs 7 = [(0, 7), (1, 6), (2, 5), (3, 4)] := rfl
private theorem pairs_8 : pairs 8 = [(1, 7), (2, 6), (3, 5)] := rfl
private theorem pairs_9 : pairs 9 = [(2, 7), (3, 6), (4, 5)] := rfl
private theorem pairs_10 : pairs 10 = [(3, 7), (4, 6)] := rfl
private theorem pairs_11 : pairs 11 = [(4, 7), (5, 6)] := rfl
private theorem pairs_12 : pairs 12 = [(5, 7)] := rfl
private theorem pairs_13 : pairs 13 = [(6, 7)] := rfl

theorem columnTotal_polynomial (s : State) :
    columnTotal s 13 = columnPolynomial (2 ^ 64) (fun i => (s.gpr inputs[i]!).toNat) := by
  simp only [columnTotal, Nat.reduceAdd, pairs_1, pairs_2, pairs_3, pairs_4, pairs_5, pairs_6, pairs_7, pairs_8, pairs_9, pairs_10, pairs_11, pairs_12, pairs_13,
    List.length_cons, List.length_nil, pairSum, pairValue,
    List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.zero_add]
  simp only [columnPolynomial, ← Nat.pow_mul]

theorem columnTotal_cross (s : State) :
    columnTotal s 13 = Square.cross (2 ^ 64) (fun i => (s.gpr inputs[i]!).toNat) 8 :=
  (columnTotal_polynomial s).trans (columnPolynomial_cross _ _)

end VG.Proof.Bignum.AArch64.SquareEight
