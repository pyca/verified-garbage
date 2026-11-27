module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
public import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-! ### `Weierstrass.X86.MontBrainpoolP512r1`, which only this module used -/

section

/-!
# Montgomery arithmetic modulo brainpoolP512r1's `p` and `n`, as functions, on x86 (32-bit): verified

brainpoolP512r1's moduli, in eight 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Impl.Weierstrass.Mont

theorem brainpoolp512r1p_ok : FnOk brainpoolp512r1p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem brainpoolp512r1n_ok : FnOk brainpoolp512r1n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

end VG.Proof.Weierstrass.X86.Mont

end

end

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
  omega_using [this]

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
