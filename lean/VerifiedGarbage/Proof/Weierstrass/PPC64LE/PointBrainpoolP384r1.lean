module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # BrainpoolP384r1's point addition and doubling as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont

theorem brainpoolp384r1_add_ct : ConstantTime isa (sumPPC Spec.Weierstrass.Point.brainpoolp384r1 false).pre (sumPPC Spec.Weierstrass.Point.brainpoolp384r1 false).pub
    (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP Spec.Weierstrass.Point.brainpoolp384r1) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem brainpoolp384r1_double_ct : ConstantTime isa (sumPPC Spec.Weierstrass.Point.brainpoolp384r1 true).pre (sumPPC Spec.Weierstrass.Point.brainpoolp384r1 true).pub
    (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP Spec.Weierstrass.Point.brainpoolp384r1) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem brainpoolp384r1_add_verified (hF : Fermat Spec.Weierstrass.Point.brainpoolp384r1.p) :
    Verified PPC64LE.target (pointAdd Spec.Weierstrass.Point.brainpoolp384r1) (Spec.Weierstrass.Point.brainpoolp384r1.addContract PPC64LE.abi) :=
  sum_verified Spec.Weierstrass.Point.brainpoolp384r1 brainpoolp384r1p_ok (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false
    brainpoolp384r1_add_ct

theorem brainpoolp384r1_double_verified (hF : Fermat Spec.Weierstrass.Point.brainpoolp384r1.p) :
    Verified PPC64LE.target (pointDouble Spec.Weierstrass.Point.brainpoolp384r1) (Spec.Weierstrass.Point.brainpoolp384r1.doubleContract PPC64LE.abi) :=
  sum_verified Spec.Weierstrass.Point.brainpoolp384r1 brainpoolp384r1p_ok (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true
    brainpoolp384r1_double_ct

end VG.Proof.Weierstrass.PPC64LE.Point
