module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_p224_mul` on PPC64LE: `Verified`

`mul_verified` for P-224 (`p224_ok`), with the function's constant time by
taint tracking (only the pointer, in `r3`, public: every address is `r3`
plus a constant or a counter, and the only branches are on loop counters)
and a state satisfying the precondition (`mulSatState`: the constants and `G`
in Montgomery's form at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P224.Mul

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE VG.Proof

/-- P-224's curve of `Proof/Weierstrass/MulContract.lean`: the one its code has. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p224

theorem C_eq : C = mulCurve p224 "p224" "P-224" := rfl

theorem mul_ct : ConstantTime isa (mulPPC C).pre (mulPPC C).pub mulP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

theorem sat_consts : C.ConstsOk 0x1000 (mulSatMem p224) := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (mulCurve p224 "p224" "P-224").toPoint.coordAt (mulSatMem p224) 0x1000 (p224.sl RX) =
    p224.mont p224.C.gx := by decide +kernel

theorem sat_y : (mulCurve p224 "p224" "P-224").toPoint.coordAt (mulSatMem p224) 0x1000 (p224.sl RY) =
    p224.mont p224.C.gy := by decide +kernel

theorem sat_point (hL : Weierstrass.Law Spec.P224.curve) :
    (mulCurve p224 "p224" "P-224").PointOk 0x1000 (mulSatMem p224) :=
  mulSat_point p224_ok hL sat_x sat_y

theorem sat_pre (hL : Weierstrass.Law Spec.P224.curve) : (C.mulInRangeContract PPC64LE.abi).pre (mulSatState p224) :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, PPC64LE.abi, PPC64LE.argRegs, mulSatState]
    exact ⟨by decide, sat_consts, sat_point hL⟩)

/-- `vg_p224_mul` on PPC64LE. -/
theorem mul_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target mulP224 (C.mulInRangeContract PPC64LE.abi) :=
  VG.Proof.Ecdsa.PPC64LE.mul_verified (curve := "p224") (desc := "P-224") p224_ok (by decide) hL mul_ct
    ⟨_, sat_pre hL⟩

end VG.Proof.Ecdsa.PPC64LE.P224.Mul
