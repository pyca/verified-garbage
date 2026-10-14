module

public import VerifiedGarbage.Impl.Secp256k1.Point
meta import VerifiedGarbage.Impl.Secp256k1.Point

public import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Spec.Secp256k1
meta import VerifiedGarbage.Spec.Secp256k1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.X25519.X86.Column
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Spec.Rc2

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): secp256k1

secp256k1 is a curve the functions support, as the curves of
`PointCurves.lean` are: its prime's Montgomery functions (`FnOk`), and the
functions' constant time by taint tracking (`τP`). Apart from the other
curves', so that adding it rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG.Impl.Secp256k1 (point)

open VG VG.X86 VG.Impl.Weierstrass.X86.Point VG.Proof.Weierstrass.X86.Mont Spec.Weierstrass.Point
open VG.Proof.Weierstrass.Point (Fermat)

theorem secp256k1_fn : FnOk (modP point) :=
  FnOk.of_eq secp256k1p_ok rfl (by simp only [Spec.Weierstrass.Mont.secp256k1p, point])

theorem secp256k1_add_ct :
    ConstantTime isa (sumX86 point false).pre (sumX86 point false).pub
      (fn (modP point) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem secp256k1_double_ct :
    ConstantTime isa (sumX86 point true).pre (sumX86 point true).pub
      (fn (modP point) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem secp256k1_add_verified (hF : Fermat point.p) :
    Verified X86.target (pointAdd point) (point.addContract X86.abi 20) :=
  sum_verified point secp256k1_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF
    false secp256k1_add_ct

theorem secp256k1_double_verified (hF : Fermat point.p) :
    Verified X86.target (pointDouble point) (point.doubleContract X86.abi 20) :=
  sum_verified point secp256k1_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF
    true secp256k1_double_ct

end VG.Proof.Weierstrass.X86.Point
