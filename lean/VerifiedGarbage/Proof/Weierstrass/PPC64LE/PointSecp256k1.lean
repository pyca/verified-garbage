module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
public import VerifiedGarbage.Impl.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Secp256k1.Point

/-! # Secp256k1's point addition and doubling as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont

theorem secp256k1_add_ct : ConstantTime isa (sumPPC VG.Impl.Secp256k1.point false).pre (sumPPC VG.Impl.Secp256k1.point false).pub
    (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP VG.Impl.Secp256k1.point) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem secp256k1_double_ct : ConstantTime isa (sumPPC VG.Impl.Secp256k1.point true).pre (sumPPC VG.Impl.Secp256k1.point true).pub
    (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP VG.Impl.Secp256k1.point) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem secp256k1_add_verified (hF : Fermat VG.Impl.Secp256k1.point.p) :
    Verified PPC64LE.target (pointAdd VG.Impl.Secp256k1.point) (VG.Impl.Secp256k1.point.addContract PPC64LE.abi) :=
  sum_verified VG.Impl.Secp256k1.point secp256k1p_ok (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false
    secp256k1_add_ct

theorem secp256k1_double_verified (hF : Fermat VG.Impl.Secp256k1.point.p) :
    Verified PPC64LE.target (pointDouble VG.Impl.Secp256k1.point) (VG.Impl.Secp256k1.point.doubleContract PPC64LE.abi) :=
  sum_verified VG.Impl.Secp256k1.point secp256k1p_ok (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true
    secp256k1_double_ct

end VG.Proof.Weierstrass.PPC64LE.Point
