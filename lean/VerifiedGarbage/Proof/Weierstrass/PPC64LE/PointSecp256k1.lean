module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Point0
public import VerifiedGarbage.Impl.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointVerified
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Point0
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Secp256k1.Point

/-! # Secp256k1's point addition and doubling as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont

theorem secp256k1_double0_ct : ConstantTime isa (pt0PPC VG.Impl.Secp256k1.point true).pre
    (pt0PPC VG.Impl.Secp256k1.point true).pub (fn0 (modP VG.Impl.Secp256k1.point) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem secp256k1_add0m_ct : ConstantTime isa (pt0PPC VG.Impl.Secp256k1.point false).pre
    (pt0PPC VG.Impl.Secp256k1.point false).pub (fn0 (modP VG.Impl.Secp256k1.point) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem secp256k1_double0_verified (hF : Fermat VG.Impl.Secp256k1.point.p) :
    Verified PPC64LE.target (pointDouble0 VG.Impl.Secp256k1.point) (VG.Impl.Secp256k1.point.double0Contract PPC64LE.abi) :=
  pt0_verified VG.Impl.Secp256k1.point secp256k1p_ok (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) hF true secp256k1_double0_ct

theorem secp256k1_add0m_verified (hF : Fermat VG.Impl.Secp256k1.point.p) :
    Verified PPC64LE.target (pointAdd0m VG.Impl.Secp256k1.point) (VG.Impl.Secp256k1.point.add0mContract PPC64LE.abi) :=
  pt0_verified VG.Impl.Secp256k1.point secp256k1p_ok (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) hF false secp256k1_add0m_ct

end VG.Proof.Weierstrass.PPC64LE.Point
