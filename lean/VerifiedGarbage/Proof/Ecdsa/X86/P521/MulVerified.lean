module

public import VerifiedGarbage.Proof.Ecdsa.X86.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P521.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulLit
import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Ecdsa.X86.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# `vg_p521_mul` on x86 (32-bit): `Verified`

`mul_verified` for P-521 (`p521_ok`), with the function's stack (its calls'
20 bytes), its constant time by taint tracking (only the stack pointer and
the argument public: every address is the argument plus a constant or a
counter, and the only branches are on loop counters) and a state satisfying
the precondition (`mulSatState`: the constants and `G` in Montgomery's form
at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P521.Mul

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof
open VG.Proof.Weierstrass.X86 (SpOk)

/-- P-521's curve of `Proof/Weierstrass/MulContract.lean`: the one its code has. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p521

theorem C_eq : C = mulCurve p521 "p521" "P-521" := rfl

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem mul_sp : SpOk mulP521 20 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem mul_ct : ConstantTime isa (mulX86 C).pre (mulX86 C).pub mulP521 :=
  VG.Taint.constantTime (A := VG.X86.taint) Weierstrass.X86.Point.τP (fun _ _ h₁ h₂ hp => agreeM h₁ h₂ hp)
    (by native_taint_decide)

theorem sat_consts : C.ConstsOk 0 (mulSatMem p521) := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (mulCurve p521 "p521" "P-521").toPoint.coordAt (mulSatMem p521) 0 (p521.sl RX) =
    p521.mont p521.C.gx := by decide +kernel

theorem sat_y : (mulCurve p521 "p521" "P-521").toPoint.coordAt (mulSatMem p521) 0 (p521.sl RY) =
    p521.mont p521.C.gy := by decide +kernel

theorem sat_point (hL : Weierstrass.Law Spec.P521.curve) :
    (mulCurve p521 "p521" "P-521").PointOk 0 (mulSatMem p521) :=
  mulSat_point p521_ok hL sat_x sat_y

theorem sat_pre (hL : Weierstrass.Law Spec.P521.curve) : (C.mulInRangeContract X86.abi 20).pre (mulSatState p521) :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      mulSatState]
    exact ⟨by decide, sat_consts, sat_point hL⟩)

/-- `vg_p521_mul` on x86. -/
theorem mul_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified X86.target mulP521 (C.mulInRangeContract X86.abi 20) :=
  VG.Proof.Ecdsa.X86.mul_verified (curve := "p521") (desc := "P-521") p521_ok hL mul_sp mul_ct (sat_pre hL)

end VG.Proof.Ecdsa.X86.P521.Mul
