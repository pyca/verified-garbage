module
public import VerifiedGarbage.Impl.Bignum.AArch64.WideLoops
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath

import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem diagonal_finish_ok {s : State} {B : Addr} {Z A eb k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B A) (h9 : s.gpr .x9 = off B eb)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (8*k)) (h7 : s.gpr .x7 = 0)
    (hk : 0 < k) (hk' : k < 2 ^ 56) (hA : A+8*(16*k+2) ≤ Z) (hb : eb+64*k ≤ Z)
    (sep : eb+64*k ≤ A ∨ A+8*(16*k+2) ≤ eb)
    (hv : wv s.mem B A (16*k+2) = Square.crossValue s.mem B eb (8*k)) :
    WP isa VG.Impl.Bignum.AArch64.WideLoops.diagonal s fun t =>
      wv t.mem B A (16*k) = wv s.mem B eb (8*k) * wv s.mem B eb (8*k) ∧
      Outside B A (8*(16*k+2)) s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s t := by
  have hsmall : Square.crossValue s.mem B eb (8*k) < 2 ^ (64*(16*k)) := by
    simpa only [show 128*(8*k) = 64*(16*k) by omega] using cross_words_lt_full s.mem B eb (8*k)
  have hlo := ProductEight.low_value hv hsmall
  have h12' : s.gpr .x12 = BitVec.ofNat 64 (4*(2*k)) := by
    simpa only [show 4*(2*k) = 8*k by omega] using h12
  refine WP.mono (WideLoops.diagonal_ok hs h8 h9 h12' h7 (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t ⟨htv, hto, _, kt⟩ => ?_
  have hlen : 2*(8*k) = 16*k := by omega
  have hw : 4*(2*k) = 8*k := by omega
  simp only [hw, hlen] at htv hto
  rw [hlo] at htv
  have hprod := htv.trans (Square.square_decomposition s.mem B eb (8*k))
  have hbnd := Nat.mul_lt_mul_of_lt_of_lt (wv_lt s.mem B eb (8*k)) (wv_lt s.mem B eb (8*k))
  have hp : 2 ^ (64*(8*k)) * 2 ^ (64*(8*k)) = 2 ^ (64*(16*k)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hp] at hbnd
  exact ⟨ProductEight.low_value hprod hbnd, hto.mono (by omega) (by omega), kt⟩

end VG.Proof.Bignum.AArch64.SquareEight
