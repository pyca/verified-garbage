module

import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontBrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Weierstrass.X86.PointContract
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P192
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P224
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P256
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P384
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.X86.Chain
meta import VerifiedGarbage.Proof.Mont.X86.Csub
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.P256Red
meta import VerifiedGarbage.Proof.Mont.X86.RedRow
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.SparseShift
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
meta import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Spec.Rc2

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): brainpoolP256r1

brainpoolP256r1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`FnOk`), and the
functions' constant time by taint tracking (`τP`). Apart from the other
curves', so that adding it rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.Impl.Weierstrass.X86.Point VG.Proof.Weierstrass.X86.Mont Spec.Weierstrass.Point
open VG.Proof.Weierstrass.Point (Fermat)

theorem brainpoolp256r1_fn : FnOk (modP brainpoolp256r1) :=
  FnOk.of_eq brainpoolp256r1p_ok rfl (by simp only [Spec.Weierstrass.Mont.brainpoolp256r1p, brainpoolp256r1])

theorem brainpoolp256r1_add_ct :
    ConstantTime isa (sumX86 brainpoolp256r1 false).pre (sumX86 brainpoolp256r1 false).pub
      (fn (modP brainpoolp256r1) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by native_taint_decide)

theorem brainpoolp256r1_double_ct :
    ConstantTime isa (sumX86 brainpoolp256r1 true).pre (sumX86 brainpoolp256r1 true).pub
      (fn (modP brainpoolp256r1) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by native_taint_decide)

theorem brainpoolp256r1_add_verified (hF : Fermat brainpoolp256r1.p) :
    Verified X86.target (pointAdd brainpoolp256r1) (brainpoolp256r1.addContract X86.abi 20) :=
  sum_verified brainpoolp256r1 brainpoolp256r1_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF
    false brainpoolp256r1_add_ct

theorem brainpoolp256r1_double_verified (hF : Fermat brainpoolp256r1.p) :
    Verified X86.target (pointDouble brainpoolp256r1) (brainpoolp256r1.doubleContract X86.abi 20) :=
  sum_verified brainpoolp256r1 brainpoolp256r1_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF
    true brainpoolp256r1_double_ct

end VG.Proof.Weierstrass.X86.Point
