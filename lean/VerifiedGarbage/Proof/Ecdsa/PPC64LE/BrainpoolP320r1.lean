module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LE
import VerifiedGarbage.Proof.BrainpoolP320r1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# brainpoolP320r1's configuration of the ECDSA code on PPC64LE

`brainpoolp320r1_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): five 64-bit words per number, and no bit of a 40-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem brainpoolp320r1_nBits : Spec.Ecdsa.nBits brainpoolp320r1.C = 320 := by
  show Spec.BrainpoolP320r1.curve.n.log2 + 1 = 320
  have h₁ : 319 ≤ Spec.BrainpoolP320r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP320r1.curve.n.log2 < 320 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- No bit of a hash of `40` bytes is dropped. -/
theorem brainpoolp320r1_sh : brainpoolp320r1.sh = 0 := by
  show 8 * 40 - Spec.Ecdsa.nBits brainpoolp320r1.C = 0
  rw [brainpoolp320r1_nBits]

theorem brainpoolp320r1_ok : CfgOk brainpoolp320r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP320r1.onCurve_G
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
  sh := by rw [brainpoolp320r1_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.brainpoolp320r1p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.brainpoolp320r1n_ok
  fnk := rfl
  fnm := rfl
  mulNf := fun _ h => nomatch h
  chainP := .of_check (by decide +kernel)
  chainN := .of_check (by decide +kernel)

end VG.Proof.Ecdsa.PPC64LE
