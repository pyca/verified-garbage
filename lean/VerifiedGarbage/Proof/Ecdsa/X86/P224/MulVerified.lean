module

public import VerifiedGarbage.Proof.Ecdsa.X86.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P224.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P224.MulLit
import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Ecdsa.X86.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.MulLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# `vg_p224_mul` on x86 (32-bit): `Verified`

`mul_verified` for P-224 (`p224_ok`), with the function's stack (its calls'
20 bytes), its constant time by taint tracking (only the stack pointer and
the argument public: every address is the argument plus a constant or a
counter, and the only branches are on loop counters) and a state satisfying
the precondition (`mulSatState`: the constants and `G` in Montgomery's form
at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P224.Mul

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof
open VG.Proof.Weierstrass.X86 (SpOk)

/-- P-224's curve of `Proof/Weierstrass/MulContract.lean`: the one its code has. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p224

theorem C_eq : C = mulCurve p224 "p224" "P-224" := rfl

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem mul_sp : SpOk mulP224 20 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem mul_ct : ConstantTime isa (mulX86 C).pre (mulX86 C).pub mulP224 :=
  VG.Taint.constantTime (A := VG.X86.taint) Weierstrass.X86.Point.τP (fun _ _ h₁ h₂ hp => agreeM h₁ h₂ hp)
    (by native_taint_decide)

theorem sat_consts : C.ConstsOk 0 (mulSatMem p224) := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (mulCurve p224 "p224" "P-224").toPoint.coordAt (mulSatMem p224) 0 (p224.sl RX) =
    p224.mont p224.C.gx := by decide +kernel

theorem sat_y : (mulCurve p224 "p224" "P-224").toPoint.coordAt (mulSatMem p224) 0 (p224.sl RY) =
    p224.mont p224.C.gy := by decide +kernel

theorem sat_point (hL : Weierstrass.Law Spec.P224.curve) :
    (mulCurve p224 "p224" "P-224").PointOk 0 (mulSatMem p224) :=
  mulSat_point p224_ok hL sat_x sat_y

theorem sat_pre (hL : Weierstrass.Law Spec.P224.curve) : (C.mulInRangeContract X86.abi 20).pre (mulSatState p224) :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      mulSatState]
    exact ⟨by decide, sat_consts, sat_point hL⟩)

/-- `vg_p224_mul` on x86. -/
theorem mul_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified X86.target mulP224 (C.mulInRangeContract X86.abi 20) :=
  VG.Proof.Ecdsa.X86.mul_verified (curve := "p224") (desc := "P-224") p224_ok hL mul_sp mul_ct (sat_pre hL)

end VG.Proof.Ecdsa.X86.P224.Mul
