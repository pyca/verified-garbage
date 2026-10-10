import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Secp256k1.Prime
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface

/-! # secp256k1 parameters for the AArch64 arithmetic -/

namespace VG.Proof.Ecdsa.AArch64.Secp256k1

open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem secp256k1_nBits : Spec.Ecdsa.nBits secp256k1.C = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h1 : 255 ≤ Spec.Secp256k1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.Secp256k1.curve.n.log2 < 256 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem secp256k1_sh : secp256k1.sh = 0 := by
  unfold Cfg.sh
  rw [secp256k1_nBits]
  rfl

theorem secp256k1_ok (hI : Weierstrass.AArch64.InvSounds) : BaseCfgOk secp256k1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.Secp256k1.onCurve_G
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
  sh := by rw [secp256k1_sh]; decide
  n4 := by decide
  sound_p := hI Proof.Secp256k1.p_prime
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.Secp256k1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  call_p := fun _ _ h => nomatch (callOf_small (by decide)).symm.trans h
  call_n := callOf_small (by decide)

end VG.Proof.Ecdsa.AArch64.Secp256k1
