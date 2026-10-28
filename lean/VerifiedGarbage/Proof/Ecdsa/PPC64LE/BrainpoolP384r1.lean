module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# brainpoolP384r1's configuration of the ECDSA code on PPC64LE

`brainpoolp384r1_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): six 64-bit words per number, and no bit of a 48-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits brainpoolp384r1.C = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP384r1.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `48` bytes is dropped. -/
theorem brainpoolp384r1_sh : brainpoolp384r1.sh = 0 := by
  show 8 * 48 - Spec.Ecdsa.nBits brainpoolp384r1.C = 0
  rw [brainpoolp384r1_nBits]

theorem brainpoolp384r1_ok : CfgOk brainpoolp384r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP384r1.onCurve_G
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
  sh := by rw [brainpoolp384r1_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.brainpoolp384r1p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.brainpoolp384r1n_ok
  fnk := rfl
  fnm := rfl
  mulNf := fun _ h => nomatch h

end VG.Proof.Ecdsa.PPC64LE
