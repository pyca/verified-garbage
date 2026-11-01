module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointContract
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Complete point addition and doubling as functions, on PPC64LE: verified

`fn (modP C) dbl` meets the contract of its `Api` (`sum_verified`), given
its constant time, and Fermat's little theorem follows from a curve's group
law (`fermat_of_law`), as on 32-bit ARM.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont

/-- `addContract` (`dbl` false) or `doubleContract`. -/
def sumC (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) : Contract PPC64LE.isa :=
  Impl.Weierstrass.Point.sig.contract PPC64LE.abi
    (pre := fun ws m => C.sumPre (Impl.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ws m)
    (post := fun ws m m' _ => C.sumPost (Impl.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ws m m')

/-- A state satisfying the preconditions. -/
def satPt : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-- Zero memory satisfies the precondition. -/
theorem pre_zero (C : Impl.Weierstrass.Point.Curve) (hp : 0 < C.p) (ws : Addr) (q : Nat) :
    C.Below (C.pointAt (fun _ => 0) ws (Impl.Weierstrass.Point.pAt C.k)) ∧ C.Below (C.pointAt (fun _ => 0) ws q) ∧
      C.ConstsBelow ws (fun _ => 0) := by
  have hz : ∀ o, C.coordAt (fun _ => 0) ws o = 0 := fun o => numAt_zero _ _ _
  simp only [Impl.Weierstrass.Point.Curve.Below, Impl.Weierstrass.Point.Curve.pointAt,
    Impl.Weierstrass.Point.Curve.ConstsBelow, hz]
  omega

/-- `vg_<curve>_point_add` (`dbl` false) or `vg_<curve>_point_double` meets
its contract, given its constant time. -/
theorem sum_verified (C : Impl.Weierstrass.Point.Curve) (hM : ModOk C.k C.p) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (dbl : Bool)
    (hct : ConstantTime isa (sumPPC C dbl).pre (sumPPC C dbl).pub (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP C) dbl)) :
    Verified PPC64LE.target (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP C) dbl) (sumC C dbl) :=
  Verified.of_correct (sum_ppc hM hk3 hk6 hodd h1 hF dbl) hct
    { pre := by sig_implies_pre [sumC, Impl.Weierstrass.Point.Curve.sumPre, Impl.Weierstrass.Point.Curve.sumPost,
        Impl.Weierstrass.Point.sig, sumPPC, Impl.Weierstrass.Point.Curve.ConstsBelow, PPC64LE.abi, PPC64LE.argRegs]
      post := by sig_implies_post [sumC, Impl.Weierstrass.Point.Curve.sumPre, Impl.Weierstrass.Point.Curve.sumPost,
        Impl.Weierstrass.Point.sig, sumPPC, Impl.Weierstrass.Point.Curve.ConstsBelow, PPC64LE.abi, PPC64LE.argRegs]
      pub := by sig_implies_pub [sumC, Impl.Weierstrass.Point.Curve.sumPre, Impl.Weierstrass.Point.Curve.sumPost,
        Impl.Weierstrass.Point.sig, sumPPC, Impl.Weierstrass.Point.Curve.ConstsBelow, PPC64LE.abi, PPC64LE.argRegs]
      sat := ⟨satPt, by
        sig_reduce [Sig.wfPre, sumC, Impl.Weierstrass.Point.sig, PPC64LE.abi, PPC64LE.argRegs, satPt]
        refine ⟨trivial, rfl, rfl, by simp, by simp, by simp, ?_⟩
        exact pre_zero C (by omega) _ _⟩ }

/-- Fermat's little theorem in `Fin p` from the curve's group law: `1 =
(1 Z) Z^(p-2)` (`Law.x_eq` for the representative `(Z : 0 : Z)` of the pair
`(1, 0)`). -/
theorem fermat_of_law {CW : Spec.Weierstrass.Curve} (hL : VG.Proof.Weierstrass.Law CW) : Fermat CW.p :=
  fun z hz => by
    rw [VG.Proof.Weierstrass.pow_eq_npow]
    have h : VG.Proof.Weierstrass.Rep CW (1 * z) (0 * z) z (.affine 1 0) := ⟨hz, rfl, rfl⟩
    have e := hL.x_eq h
    rw [e]; grind

end VG.Proof.Weierstrass.PPC64LE.Point
