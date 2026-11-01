module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.MulLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.MulLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_p256_mul` on PPC64LE: `Verified`

`mul_verified` for P-256 (`p256_ok`), with the function's constant time by
taint tracking (only the pointer, in `r3`, public: every address is `r3`
plus a constant or a counter, and the only branches are on loop counters)
and a state satisfying the precondition (`mulSatState`: the constants and `G`
in Montgomery's form at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P256.Mul

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE VG.Proof

/-- P-256's curve of `Proof/Weierstrass/MulContract.lean`: the one its code has. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p256

theorem C_eq : C = mulCurve p256 "p256" "P-256" := rfl

theorem mul_ct : ConstantTime isa (mulPPC C).pre (mulPPC C).pub mulP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem sat_consts : C.ConstsOk 0x1000 (mulSatMem p256) := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (mulCurve p256 "p256" "P-256").toPoint.coordAt (mulSatMem p256) 0x1000 (p256.sl RX) =
    p256.mont p256.C.gx := by decide +kernel

theorem sat_y : (mulCurve p256 "p256" "P-256").toPoint.coordAt (mulSatMem p256) 0x1000 (p256.sl RY) =
    p256.mont p256.C.gy := by decide +kernel

theorem sat_point (hL : Weierstrass.Law Spec.P256.curve) :
    (mulCurve p256 "p256" "P-256").PointOk 0x1000 (mulSatMem p256) :=
  mulSat_point p256_ok hL sat_x sat_y

theorem sat_pre (hL : Weierstrass.Law Spec.P256.curve) : (C.mulInRangeContract PPC64LE.abi).pre (mulSatState p256) :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, PPC64LE.abi, PPC64LE.argRegs, mulSatState]
    exact ⟨by decide, sat_consts, sat_point hL⟩)

/-- `vg_p256_mul` on PPC64LE. -/
theorem mul_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified PPC64LE.target mulP256 (C.mulInRangeContract PPC64LE.abi) :=
  VG.Proof.Ecdsa.PPC64LE.mul_verified (curve := "p256") (desc := "P-256") p256_ok (by decide) hL mul_ct
    ⟨_, sat_pre hL⟩

end VG.Proof.Ecdsa.PPC64LE.P256.Mul
