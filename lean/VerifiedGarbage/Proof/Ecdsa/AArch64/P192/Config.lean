import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.P192.OrderPrime
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec

/-! # p192 parameters for the AArch64 arithmetic -/

namespace VG.Proof.Ecdsa.AArch64.P192

open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem p192_nBits : Spec.Ecdsa.nBits p192.C = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h1 : 191 ≤ Spec.P192.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P192.curve.n.log2 < 192 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `24` bytes is dropped. -/
theorem p192_sh : p192.sh = 0 := by
  unfold Cfg.sh
  rw [p192_nBits]
  rfl

theorem p192_ok (hI : Weierstrass.AArch64.InvSounds) : BaseCfgOk p192 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P192.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  n2 := by decide
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [p192_sh]; decide
  n4 := by decide
  sound_p := hI Proof.P192.p_prime
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.P192.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  call_p := fun _ _ h => nomatch (callOf_small (by decide)).symm.trans h
  call_n := callOf_small (by decide)

end VG.Proof.Ecdsa.AArch64.P192
