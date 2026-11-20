module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
import VerifiedGarbage.Proof.BrainpoolP320r1.Point
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.BrainpoolP320r1.Point
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP320r1
public import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP320r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224

/-! ### `Weierstrass.X86.MontBrainpoolP320r1`, which only this module used -/

section

/-!
# Montgomery arithmetic modulo brainpoolP320r1's `p` and `n`, as functions, on x86 (32-bit): verified

brainpoolP320r1's moduli, in five 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Impl.Weierstrass.Mont

theorem brainpoolp320r1p_ok : FnOk brainpoolp320r1p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem brainpoolp320r1n_ok : FnOk brainpoolp320r1n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

end VG.Proof.Weierstrass.X86.Mont

end

end

/-!
# ECDSA over brainpoolP320r1 on x86 (32-bit): the curve

brainpoolP320r1 is a curve the proofs support (`brainpoolp320r1_ok`), with the bits of its order;
and the hints of the constant-time checks of the functions over it (`weak`).
The signature, with the curve's comb, is `Proof/Ecdsa/X86/BrainpoolP320r1/Comb.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.BrainpoolP320r1

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp320r1_nBits : 64 * brainpoolp320r1.n ≤ Spec.Ecdsa.nBits brainpoolp320r1.C := by
  show 320 ≤ Spec.BrainpoolP320r1.curve.n.log2 + 1
  have : 319 ≤ Spec.BrainpoolP320r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega_using [this]

/-- No bit of a hash of `40` bytes is dropped. -/
theorem brainpoolp320r1_sh : brainpoolp320r1.sh = 0 := by
  have h : 64 * 5 ≤ Spec.Ecdsa.nBits brainpoolp320r1.C := brainpoolp320r1_nBits
  show 8 * 40 - Spec.Ecdsa.nBits brainpoolp320r1.C = 0; omega_using [h]

theorem brainpoolp320r1_ok : CfgOk brainpoolp320r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP320r1.onCurve_G
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
  sh := by rw [brainpoolp320r1_sh]; decide

  inv_p h := False.elim ((by decide : ¬ (brainpoolp320r1.n = 4 ∧ brainpoolp320r1.C.len = 32)) h)
  inv_n h := False.elim ((by decide : ¬ (brainpoolp320r1.n = 4 ∧ brainpoolp320r1.C.len = 32)) h)
  fp := ⟨rfl, rfl, Mont.brainpoolp320r1p_ok⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp320r1n_ok⟩

/-- The hints of the constant-time checks forget the public slots of memory
and the words known to hold base addresses (`native_taint_decide_weak`): no address
or branch depends on a value loaded from the working space, and the kernel
evaluates every instruction faster with less to look through. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with slots := .empty, wbases := [] } else τ

end VG.Proof.Ecdsa.X86.BrainpoolP320r1
