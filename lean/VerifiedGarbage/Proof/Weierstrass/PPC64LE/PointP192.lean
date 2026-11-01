module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # P192's point addition and doubling as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont

theorem p192_add_ct : ConstantTime isa (sumPPC Impl.Weierstrass.Point.p192 false).pre (sumPPC Impl.Weierstrass.Point.p192 false).pub
    (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP Impl.Weierstrass.Point.p192) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem p192_double_ct : ConstantTime isa (sumPPC Impl.Weierstrass.Point.p192 true).pre (sumPPC Impl.Weierstrass.Point.p192 true).pub
    (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP Impl.Weierstrass.Point.p192) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem p192_add_verified (hF : Fermat Impl.Weierstrass.Point.p192.p) :
    Verified PPC64LE.target (pointAdd Impl.Weierstrass.Point.p192) (Impl.Weierstrass.Point.p192.addContract PPC64LE.abi) :=
  sum_verified Impl.Weierstrass.Point.p192 p192p_ok (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false
    p192_add_ct

theorem p192_double_verified (hF : Fermat Impl.Weierstrass.Point.p192.p) :
    Verified PPC64LE.target (pointDouble Impl.Weierstrass.Point.p192) (Impl.Weierstrass.Point.p192.doubleContract PPC64LE.abi) :=
  sum_verified Impl.Weierstrass.Point.p192 p192p_ok (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true
    p192_double_ct

end VG.Proof.Weierstrass.PPC64LE.Point
