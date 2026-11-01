module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontBrainpoolP384r1
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.BrainpoolP384r1.Prime
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Weierstrass.CombLay

/-! # brainpoolP384r1 parameters for the AArch64 arithmetic -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP384r1

open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits brainpoolp384r1.C = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h1 : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP384r1.curve.n.log2 < 384 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `48` bytes is dropped. -/
theorem brainpoolp384r1_sh : brainpoolp384r1.sh = 0 := by
  have := brainpoolp384r1_nBits; have : brainpoolp384r1.C.len = 48 := rfl; unfold Cfg.sh; omega

theorem brainpoolp384r1_ok (hI : Weierstrass.AArch64.InvSounds) : BaseCfgOk brainpoolp384r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP384r1.onCurve_G
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
  sh := by rw [brainpoolp384r1_sh]; decide
  n4 := by decide
  sound_p := hI Proof.BrainpoolP384r1.p_prime
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.BrainpoolP384r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  call_p := by
    intro f m h
    have e : Mont.callOf brainpoolp384r1.MP' = some
        (Impl.Weierstrass.Mont.brainpoolp384r1p.fn "mul", Spec.BrainpoolP384r1.p) := by decide +kernel
    rw [e] at h
    cases h
    exact ⟨rfl, Mont.brainpoolp384r1p_ok⟩
  call_n := by
    intro f m h
    have e : Mont.callOf brainpoolp384r1.MN' = some
        (Impl.Weierstrass.Mont.brainpoolp384r1n.fn "mul", Spec.BrainpoolP384r1.n) := by decide +kernel
    rw [e] at h
    cases h
    exact ⟨rfl, Mont.brainpoolp384r1n_ok⟩
  inv_at := .inr (by decide +kernel)
  inv_fn := fun _ => ⟨by decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide⟩
  padd := fun h => absurd rfl h
  check_fn := fun _ => ⟨by lit_decide, by lit_decide, by lit_decide⟩

end VG.Proof.Ecdsa.AArch64.BrainpoolP384r1
