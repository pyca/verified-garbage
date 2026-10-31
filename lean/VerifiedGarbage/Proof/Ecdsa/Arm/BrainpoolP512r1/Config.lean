module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # brainpoolP512r1's configuration for public keys and ECDH on Arm -/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp512r1_nBits : 64 * brainpoolp512r1.n ≤ Spec.Ecdsa.nBits brainpoolp512r1.C := by
  show 512 ≤ Spec.BrainpoolP512r1.curve.n.log2 + 1
  have : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `64` bytes is dropped. -/
theorem brainpoolp512r1_sh : brainpoolp512r1.sh = 0 := by
  have h : 64 * 8 ≤ Spec.Ecdsa.nBits brainpoolp512r1.C := brainpoolp512r1_nBits
  exact Nat.sub_eq_zero_of_le h

theorem brainpoolp512r1_ok : CfgOk brainpoolp512r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP512r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [brainpoolp512r1_sh]; decide
  fp := ⟨rfl, rfl, Mont.brainpoolp512r1p_ok, rfl⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp512r1n_ok, rfl⟩
  mulNf := fun _ h => nomatch h


/-- brainpoolp512r1 with its field multiplications by `vg_brainpoolp512r1_mul_mod_<p|n>_umaal`:
what `brainpoolp512r1_ok` states. -/
theorem brainpoolp512r1u_ok : CfgOk (brainpoolp512r1With true) where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP512r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by
    have h : 64 * 8 ≤ Spec.Ecdsa.nBits (brainpoolp512r1With true).C := brainpoolp512r1_nBits
    rw [show (brainpoolp512r1With true).sh = 0 from Nat.sub_eq_zero_of_le h]; decide
  fp := ⟨rfl, rfl, Mont.brainpoolp512r1p_ok, rfl⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp512r1n_ok, rfl⟩
  mulNf := fun _ h => nomatch h

/-- Either configuration. -/
theorem brainpoolp512r1With_ok (u : Bool) : CfgOk (brainpoolp512r1With u) := by
  cases u
  · exact brainpoolp512r1_ok
  · exact brainpoolp512r1u_ok
end VG.Proof.Ecdsa.Arm.BrainpoolP512r1
