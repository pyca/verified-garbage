module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Impl.Ecdsa.P384.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.P384.Point
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over P-384 on x86 (32-bit): the curve

P-384 is a curve the proofs support (`p384_ok`), with the bits of its order;
and the hints of the constant-time checks of the functions over it (`weak`).
The signature, with the curve's comb, is `Proof/Ecdsa/X86/P384/Comb.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P384

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p384_nBits : 64 * p384.n ≤ Spec.Ecdsa.nBits p384.C := by
  show 384 ≤ Spec.P384.curve.n.log2 + 1
  have : 383 ≤ Spec.P384.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega_using [this]

/-- No bit of a hash of `48` bytes is dropped. -/
theorem p384_sh : p384.sh = 0 := by
  have h : 64 * 6 ≤ Spec.Ecdsa.nBits p384.C := p384_nBits
  show 8 * 48 - Spec.Ecdsa.nBits p384.C = 0; omega_using [h]

theorem p384_ok : CfgOk p384 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
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
  sh := by rw [p384_sh]; decide

  inv_p h := False.elim ((by decide : ¬ (p384.n = 4 ∧ p384.C.len = 32)) h)
  inv_n h := False.elim ((by decide : ¬ (p384.n = 4 ∧ p384.C.len = 32)) h)
  fp := ⟨rfl, rfl, Mont.p384p_ok⟩
  fn := ⟨rfl, rfl, Mont.p384n_ok⟩

/-- The hints of the constant-time checks forget the public slots of memory
and the words known to hold base addresses (`native_taint_decide_weak`): no address
or branch depends on a value loaded from the working space, and the kernel
evaluates every instruction faster with less to look through. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with slots := .empty, wbases := [] } else τ

end VG.Proof.Ecdsa.X86.P384
