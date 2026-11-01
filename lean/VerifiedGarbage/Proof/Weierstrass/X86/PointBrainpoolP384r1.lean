module

import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP384r1
public import VerifiedGarbage.Proof.Weierstrass.X86.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.BrainpoolP384r1
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P192
import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P224
import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P256
import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P384
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP384r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointContract
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P192
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P224
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P256
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P384
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): brainpoolP384r1

brainpoolP384r1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`FnOk`), and the
functions' constant time by taint tracking (`τP`). Apart from the other
curves', so that adding it rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.Impl.Weierstrass.X86.Point VG.Proof.Weierstrass.X86.Mont Spec.Weierstrass.Point Impl.Weierstrass.Point
open VG.Proof.Weierstrass.Point (Fermat)

theorem brainpoolp384r1_fn : FnOk (modP brainpoolp384r1) :=
  FnOk.of_eq brainpoolp384r1p_ok rfl (by simp only [Impl.Weierstrass.Mont.brainpoolp384r1p, brainpoolp384r1])

theorem brainpoolp384r1_add_ct :
    ConstantTime isa (sumX86 brainpoolp384r1 false).pre (sumX86 brainpoolp384r1 false).pub
      (fn (modP brainpoolp384r1) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by native_taint_decide)

theorem brainpoolp384r1_double_ct :
    ConstantTime isa (sumX86 brainpoolp384r1 true).pre (sumX86 brainpoolp384r1 true).pub
      (fn (modP brainpoolp384r1) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by native_taint_decide)

theorem brainpoolp384r1_add_verified (hF : Fermat brainpoolp384r1.p) :
    Verified X86.target (pointAdd brainpoolp384r1) (brainpoolp384r1.addContract X86.abi 20) :=
  sum_verified brainpoolp384r1 brainpoolp384r1_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF
    false brainpoolp384r1_add_ct

theorem brainpoolp384r1_double_verified (hF : Fermat brainpoolp384r1.p) :
    Verified X86.target (pointDouble brainpoolp384r1) (brainpoolp384r1.doubleContract X86.abi 20) :=
  sum_verified brainpoolp384r1 brainpoolp384r1_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF
    true brainpoolp384r1_double_ct

end VG.Proof.Weierstrass.X86.Point
