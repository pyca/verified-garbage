module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Mont.X86.Square.CrossGuard
public import VerifiedGarbage.Proof.Mont.X86.Square.CrossBody
public import VerifiedGarbage.Proof.Mont.X86.Square.Dot
public import VerifiedGarbage.Proof.Mont.X86.Square.PairStage
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont

theorem total_eq_sum (f : Nat → Nat) (n : Nat) : total f n = NatSum.sum f n := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp only [total, ih, NatSum.succ]

theorem total_split (f : Nat → Nat) (r n : Nat) :
    total (fun j => f j % r) n + r*total (fun j => f j/r) n = total f n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, Nat.mul_add]
    have e := Nat.mod_add_div (f n) r
    omega

theorem pair_value (s : State) (W : Addr) (a : Nat) {N k : Nat} (hk : k<2*N) :
    pairLow s W a N k + 2^32*pairHigh s W a N k =
      Column.crossCoeff (fun j => w32 s.mem W (a+4*j)) N k := by
  unfold pairLow pairHigh
  rw [total_split, total_eq_sum, Column.crossCoeff_scan _ hk]
  apply NatSum.congr
  intro j hj
  have jb := hj
  unfold dotProd
  have e1 : a+4*(k+1-N)+4*j = a+4*(k+1-N+j) := by omega
  have e2 : a+4*(k-(k+1-N))-4*j = a+4*(k-(k+1-N+j)) := by
    dsimp [pairCount] at jb
    omega
  rw [e1, e2]

theorem input_value (s : State) (W : Addr) (a : Nat) {N k : Nat} (hk : k<2*N) :
    inputLow s W a N k + 2^32*inputHigh s W a N k =
      Column.coeff (fun j => w32 s.mem W (a+4*j)) (fun j => w32 s.mem W (a+4*j)) N k := by
  rw [Column.coeff_square, Column.diagCoeff_value]
  have pairs := pair_value s W a hk
  unfold inputLow inputHigh diagProduct
  by_cases even : k%2=0
  · have half : k/2<N := by omega
    simp only [even, half, and_self, ↓reduceIte]
    have div := Nat.mod_add_div (w32 s.mem W (a+4*(k/2))*w32 s.mem W (a+4*(k/2))) (2^32)
    omega
  · simp only [even, false_and, ↓reduceIte, Nat.add_zero]
    omega

theorem total_le_const (f : Nat → Nat) {n B : Nat} (h : ∀ j<n, f j≤B) : total f n≤n*B := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [total, Nat.succ_mul]
    exact Nat.add_le_add (ih (fun j hj => h j (by omega))) (h n (by omega))

theorem pair_bounds (s : State) (W : Addr) (a N k : Nat) :
    pairLow s W a N k ≤ pairCount N k*(2^32-1) ∧
    pairHigh s W a N k ≤ pairCount N k*(2^32-1) := by
  constructor
  · exact total_le_const _ (fun j _ => by have := Nat.mod_lt (dotProd s W (a+4*(k+1-N)) (a+4*(k-(k+1-N))) j) (by decide : 0<2^32); omega)
  · apply total_le_const
    intro j hj
    have left := (s.mem.readW (off W (a+4*(k+1-N)+4*j)) 32).isLt
    have right := (s.mem.readW (off W (a+4*(k-(k+1-N))-4*j)) 32).isLt
    have prod := Nat.mul_lt_mul'' left right
    have lt : dotProd s W (a+4*(k+1-N)) (a+4*(k-(k+1-N))) j / 2^32 < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 prod
    omega

theorem input_bounds (s : State) (W : Addr) (a : Nat) {N k : Nat} (hk : k<2*N) :
    inputLow s W a N k ≤ N*(2^32-1) ∧ inputHigh s W a N k ≤ N*(2^32-1) := by
  have pair := pair_bounds s W a N k
  have dl : diagProduct s W a k % 2^32 ≤ 2^32-1 := by
    have := Nat.mod_lt (diagProduct s W a k) (by decide : 0<2^32); omega
  have dh : diagProduct s W a k / 2^32 ≤ 2^32-1 := by
    have word := (s.mem.readW (off W (a+4*(k/2))) 32).isLt
    have prod := Nat.mul_lt_mul'' word word
    have lt : diagProduct s W a k / 2^32 < 2^32 := (Nat.div_lt_iff_lt_mul (by decide)).2 prod
    omega
  unfold inputLow inputHigh
  by_cases even : k%2=0
  · have count : 2*pairCount N k+1≤N := by unfold pairCount; omega
    simp only [even, ↓reduceIte]
    constructor <;> omega
  · have count : 2*pairCount N k≤N := by unfold pairCount; omega
    simp only [even, ↓reduceIte]
    constructor <;> omega

end VG.Proof.Mont.X86.Square
