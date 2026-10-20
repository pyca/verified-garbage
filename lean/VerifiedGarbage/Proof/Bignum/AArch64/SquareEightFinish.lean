module

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarry
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEightRaw
open VG.Proof.MlKem.AArch64 (Keep)

private theorem carry_weight (i j : Nat) :
    2 ^ (64*i) * 2 ^ (64*j) = 2 ^ (64*(i+j)) := by
  rw [← Nat.pow_add]
  congr 1
  omega

private theorem carry_lift {a b w r p c x : Nat}
    (hp : w*r = p) (h : a+w*(r*c) = b+w*0+w*x) : a+p*c = b+w*x := by grind

theorem finishCarry_full {s : State} {B : Addr} {Z e i n : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B (e+128*i)) (h7 : s.gpr .x7 = 0)
    (he : e+8*n ≤ Z) (hi : 16*i+15 ≤ n) :
    WP isa (.block finishCarry) s fun t =>
      wv t.mem B e n + 2 ^ (64*(16*i+15))*t.c.toNat =
        wv s.mem B e n + 2 ^ (64*(16*i+8))*(s.gpr .x10).toNat ∧
      Outside B (e+128*i+64) 56 s.mem t.mem ∧ Keep [.x13] s t := by
  have hn := hs.nowrap
  refine WP.mono (finishCarry_ok hs h16 h7 (by omega)) fun t ⟨htv, hto, kt⟩ => ?_
  have offeq : e+8*(16*i+8) = e+128*i+64 := by omega
  have hf := ProductEight.wv_window_delta (n := n) (j := 16*i+8) (k := 7)
    (by omega : e+8*n ≤ 2 ^ 64) (by omega)
    (by simpa only [offeq] using hto)
  rw [offeq] at hf
  have heq : wv t.mem B (e+128*i+64) 7 + 2 ^ (64*7)*t.c.toNat =
      wv s.mem B (e+128*i+64) 7 + 0 + (s.gpr .x10).toNat := by
    simpa only [Nat.add_zero] using htv
  have h := ProductEight.window_lift hf heq
  have hp : 2 ^ (64*(16*i+8)) * 2 ^ (64*7) = 2 ^ (64*(16*i+15)) := by
    simpa only [show 16*i+8+7 = 16*i+15 by omega] using carry_weight (16*i+8) 7
  exact ⟨carry_lift hp h, hto, kt⟩

/-- After the row's product and carry passes, the high carry vanishes from
an arithmetic bound on the complete next triangle, including maximal limbs. -/
theorem row_finish_value {m : Mem} {B : Addr} {e i old middle out carry pending : Nat}
    (h1 : old = Square.crossValue m B e (8*i) +
      2 ^ (64*(16*i))*Square.crossValue m B (e+64*i) 8)
    (h2 : middle + 2 ^ (64*(16*i+8))*pending = old +
      2 ^ (64*(8*i))*(wv m B (e+64*i) 8 * wv m B e (8*i)))
    (h3 : out + 2 ^ (64*(16*i+15))*carry = middle + 2 ^ (64*(16*i+8))*pending) :
    out = Square.crossValue m B e (8*(i+1)) ∧ carry = 0 := by
  have hv : out + 2 ^ (64*(16*i+15))*carry = Square.crossValue m B e (8*(i+1)) := by
    rw [h3, h2, h1, ← row_cross_add]
  have hb := row_cross_bound m B e i
  have hc : carry = 0 := by
    by_contra hh
    have hp := Nat.mul_le_mul_left (2 ^ (64*(16*i+15))) (show 1 ≤ carry by omega)
    simp only [Nat.mul_one] at hp
    omega
  exact ⟨by simpa only [hc, Nat.mul_zero, Nat.add_zero] using hv, hc⟩

end VG.Proof.Bignum.AArch64.SquareEight
