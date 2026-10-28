module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# brainpoolP512r1's configuration of the ECDSA code on PPC64LE

`brainpoolp512r1_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): eight 64-bit words per number, and no bit of a 64-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem brainpoolp512r1_nBits : 512 ≤ Spec.Ecdsa.nBits brainpoolp512r1.C := by
  show 512 ≤ Spec.BrainpoolP512r1.curve.n.log2 + 1
  have : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `64` bytes is dropped. -/
theorem brainpoolp512r1_sh : brainpoolp512r1.sh = 0 :=
  Nat.sub_eq_zero_of_le (show 8 * 64 ≤ _ from brainpoolp512r1_nBits)

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
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [brainpoolp512r1_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.brainpoolp512r1p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.brainpoolp512r1n_ok
  fnk := rfl
  fnm := rfl
  mulNf := fun _ h => nomatch h

end VG.Proof.Ecdsa.PPC64LE
