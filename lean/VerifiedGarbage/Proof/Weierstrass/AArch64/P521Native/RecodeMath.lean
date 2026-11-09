module

public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Framework.Omega

/-! The P-521 recoding fits exactly 105 signed windows without truncation. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass.Window5

theorem recode_below_window {k J : Nat} (bound : 4*k<32^J) :
    k+16*Window5.geom J<32^J := by
  have hg := geom_mul J
  omega_arith

theorem window_radix_decompose (b c d : Nat) (h : 5*b=c+d) :
    (32 : Nat)^b=2^c*2^d := by
  rw [show (32 : Nat)=2^5 from rfl,←Nat.pow_mul,h,Nat.pow_add]

theorem window_radix_decompose_value (b c d v : Nat) (h : 5*b=c+d) (hv : 2^d=v) :
    (32 : Nat)^b=v*2^c := by
  rw [window_radix_decompose b c d h,hv,Nat.mul_comm]

theorem p521_window_radix : (32 : Nat)^105=16*2^521 :=
  window_radix_decompose_value 105 521 4 16 (by decide) (by decide)

theorem p521_recode_bound {k : Nat} (bound : k<2^521) :
    k+16*Window5.geom 105<32^105 := by
  apply recode_below_window
  rw [p521_window_radix]
  omega_arith

end VG.Proof.Weierstrass.AArch64.P521Native
