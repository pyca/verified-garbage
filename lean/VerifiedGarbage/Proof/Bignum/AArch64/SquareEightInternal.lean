module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTile
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem internal_ok {s : State} {B : Addr} {Z eA eT i n : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B (eA+64*i))
    (h16 : s.gpr .x16 = off B (eT+128*i)) (h7 : s.gpr .x7 = 0)
    (hA : eA+64*i+64 ≤ Z) (hT : eT+8*n ≤ Z) (hi : 16*i+15 ≤ n)
    (hv : wv s.mem B eT n < 2 ^ (64*(16*i))) :
    WP isa (.block VG.Impl.Bignum.AArch64.SquareEight.code) s fun t =>
      wv t.mem B eT n = wv s.mem B eT n +
        2 ^ (64*(16*i)) * Square.crossValue s.mem B (eA+64*i) 8 ∧
      Outside B (eT+128*i) 120 s.mem t.mem ∧ Keep codeRegs s t := by
  have hn := hs.nowrap
  have hzero := zero_window_of_lt (len := 15) hi hv
  have hz := zero_window_of_lt (len := 1) (by omega) hv
  have offeq : eT+8*(16*i) = eT+128*i := by omega
  rw [offeq] at hzero hz
  refine WP.mono (code_ok hs h8 h16 hA (by omega) h7 hz) fun t ⟨htv, hto, kt⟩ => ?_
  have ho : Outside B (eT+128*i) 120 s.mem t.mem := hto.mono (by omega) (by omega)
  have hw := ProductEight.wv_window_delta (n := n) (j := 16*i) (k := 15)
    (by omega : eT+8*n ≤ 2 ^ 64) hi
    (by simpa only [offeq] using ho)
  rw [offeq, hzero, htv, Nat.mul_zero, Nat.add_zero] at hw
  exact ⟨hw, ho, kt⟩

end VG.Proof.Bignum.AArch64.SquareEight
