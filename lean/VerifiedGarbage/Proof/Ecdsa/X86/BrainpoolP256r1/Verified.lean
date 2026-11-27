module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.BrainpoolP256r1.Prime
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.BrainpoolP256r1.Point
meta import VerifiedGarbage.Proof.BrainpoolP256r1.Prime
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224

/-! ### `Weierstrass.X86.MontBrainpoolP256r1`, which only this module used -/

section

/-!
# Montgomery arithmetic modulo brainpoolP256r1's `p` and `n`, as functions, on x86 (32-bit): verified

brainpoolP256r1's moduli, in three 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Impl.Weierstrass.Mont

theorem brainpoolp256r1p_ok : FnOk brainpoolp256r1p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem brainpoolp256r1n_ok : FnOk brainpoolp256r1n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

end VG.Proof.Weierstrass.X86.Mont

end

end

/-!
# ECDSA over brainpoolP256r1 on x86 (32-bit): the curve

brainpoolP256r1 is a curve the proofs support (`brainpoolp256r1_ok`), with the bits of its order;
and the hints of the constant-time checks of the functions over it (`weak`).
The signature, with the curve's comb, is `Proof/Ecdsa/X86/BrainpoolP256r1/Comb.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.BrainpoolP256r1

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits brainpoolp256r1.C = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h1 : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP256r1.curve.n.log2 < 256 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h1, h2]

/-- No bit of a hash of `32` bytes is dropped. -/
theorem brainpoolp256r1_sh : brainpoolp256r1.sh = 0 := by
  unfold Cfg.sh
  rw [brainpoolp256r1_nBits]
  rfl

theorem brainpoolp256r1_ok (hI : Inv.InvSounds) : CfgOk brainpoolp256r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP256r1.onCurve_G
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
  sh := by rw [brainpoolp256r1_sh]; decide

  inv_p _ := ⟨@hI _ brainpoolp256r1.C.p_ne_zero Proof.BrainpoolP256r1.p_prime,
    Inv.InvOk.ofMod (by decide +kernel) Mont.brainpoolp256r1p_ok rfl rfl⟩
  inv_n _ := ⟨@hI _ brainpoolp256r1.C.n_ne_zero Proof.BrainpoolP256r1.n_prime,
    Inv.InvOk.ofMod (by decide +kernel) Mont.brainpoolp256r1n_ok rfl rfl⟩
  fp := ⟨rfl, rfl, Mont.brainpoolp256r1p_ok⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp256r1n_ok⟩

/-- The hints of the constant-time checks forget the words known to hold base
addresses (`native_taint_decide_weak`): no address depends on a value loaded from
the working space, and the kernel evaluates every instruction faster with
less to look through. They keep the public slots of memory, which the
inversions by divsteps read back (their batch counter). Inside the calls of
the field arithmetic (`τ.stk ≠ []`), they keep everything: the functions read
their pointers from the words of the call's frame. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with wbases := [] } else τ

end VG.Proof.Ecdsa.X86.BrainpoolP256r1
