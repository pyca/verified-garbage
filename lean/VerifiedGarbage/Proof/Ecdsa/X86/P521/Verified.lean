module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.P521
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Impl.Ecdsa.P521.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.P521
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.P521.Point
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over P-521 on x86 (32-bit): the curve

P-521 is a curve the proofs support (`p521_ok`), with the bits of its order;
and the hints of the constant-time checks of the functions over it (`weak`).
The signature, with the curve's comb, is `Proof/Ecdsa/X86/P521/Comb.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P521

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p521_nBits : Spec.Ecdsa.nBits p521.C = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h1 : 520 ≤ Spec.P521.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P521.curve.n.log2 < 521 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h1, h2]

/-- A hash of `66` bytes drops its last 7 bits. -/
theorem p521_sh : p521.sh = 7 := by
  unfold Cfg.sh
  rw [p521_nBits]
  rfl

theorem p521_ok : CfgOk p521 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
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
  sh := by rw [p521_sh]; decide

  inv_p h := False.elim ((by decide : ¬ (p521.n = 4 ∧ p521.C.len = 32)) h)
  inv_n h := False.elim ((by decide : ¬ (p521.n = 4 ∧ p521.C.len = 32)) h)
  fp := ⟨rfl, rfl, Mont.p521p_ok⟩
  fn := ⟨rfl, rfl, Mont.p521n_ok⟩

/-- The hints of the constant-time checks forget the words known to hold base
addresses (`native_taint_decide_weak`): no address depends on a value loaded from
the working space, and the kernel evaluates every instruction faster with
less to look through. They keep the public slots of memory, unlike P-384's:
the setup stores the top 32-bit word of the hash's slot, past its 66 bytes,
as the constant 0, and the shift of the hash reads it into `edx`, which is
public at the end of a chunk of the hint only through that slot. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with wbases := [] } else τ

end VG.Proof.Ecdsa.X86.P521
