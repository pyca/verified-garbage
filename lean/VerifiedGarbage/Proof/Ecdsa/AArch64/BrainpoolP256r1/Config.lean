module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.BrainpoolP256r1.Prime
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Weierstrass.CombLay

/-! # brainpoolP256r1 parameters for the AArch64 arithmetic -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1

open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits brainpoolp256r1.C = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h1 : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP256r1.curve.n.log2 < 256 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem brainpoolp256r1_sh : brainpoolp256r1.sh = 0 := by
  unfold Cfg.sh
  rw [brainpoolp256r1_nBits]
  rfl

theorem brainpoolp256r1_ok (hI : Weierstrass.AArch64.InvSounds) : BaseCfgOk brainpoolp256r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP256r1.onCurve_G
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
  sh := by rw [brainpoolp256r1_sh]; decide
  n4 := by decide
  sound_p := hI Proof.BrainpoolP256r1.p_prime
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.BrainpoolP256r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  call_p := fun _ _ h => nomatch (callOf_small (by decide)).symm.trans h
  call_n := fun _ _ h => nomatch (callOf_small (by decide)).symm.trans h
  inv_at := .inr (by decide +kernel)
  inv_fn := fun _ => ⟨by decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide⟩
  padd := fun h => absurd rfl h
  check_fn := fun _ => ⟨by lit_decide, by lit_decide, by lit_decide⟩

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1
