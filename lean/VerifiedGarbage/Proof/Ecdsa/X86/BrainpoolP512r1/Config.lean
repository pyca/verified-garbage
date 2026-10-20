module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP512r1
import VerifiedGarbage.Proof.BrainpoolP512r1.Point

/-! # brainpoolP512r1's configuration for public keys and ECDH on X86 -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.BrainpoolP512r1

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

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
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [brainpoolp512r1_sh]; decide

  inv_p h := False.elim ((by decide : ¬ (brainpoolp512r1.n = 4 ∧ brainpoolp512r1.C.len = 32)) h)
  inv_n h := False.elim ((by decide : ¬ (brainpoolp512r1.n = 4 ∧ brainpoolp512r1.C.len = 32)) h)
  fp := ⟨rfl, rfl, Mont.brainpoolp512r1p_ok⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp512r1n_ok⟩


/-- Forget unused public slots in constant-time analysis hints. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with slots := .empty, wbases := [] } else τ

end VG.Proof.Ecdsa.X86.BrainpoolP512r1
