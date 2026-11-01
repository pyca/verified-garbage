module

public import VerifiedGarbage.Proof.Ecdsa.X86.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P384.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P384.MulLit
import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Ecdsa.X86.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.MulLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# `vg_p384_mul` on x86 (32-bit): `Verified`

`mul_verified` for P-384 (`p384_ok`), with the function's stack (its calls'
20 bytes), its constant time by taint tracking (only the stack pointer and
the argument public: every address is the argument plus a constant or a
counter, and the only branches are on loop counters) and a state satisfying
the precondition (`mulSatState`: the constants and `G` in Montgomery's form
at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P384.Mul

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof
open VG.Proof.Weierstrass.X86 (SpOk)

/-- P-384's curve of `Proof/Weierstrass/MulContract.lean`: the one its code has. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p384

theorem C_eq : C = mulCurve p384 "p384" "P-384" := rfl

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem mul_sp : SpOk mulP384 20 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem mul_ct : ConstantTime isa (mulX86 C).pre (mulX86 C).pub mulP384 :=
  VG.Taint.constantTime (A := VG.X86.taint) Weierstrass.X86.Point.τP (fun _ _ h₁ h₂ hp => agreeM h₁ h₂ hp)
    (by native_taint_decide)

theorem sat_consts : C.ConstsOk 0 (mulSatMem p384) := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (mulCurve p384 "p384" "P-384").toPoint.coordAt (mulSatMem p384) 0 (p384.sl RX) =
    p384.mont p384.C.gx := by decide +kernel

theorem sat_y : (mulCurve p384 "p384" "P-384").toPoint.coordAt (mulSatMem p384) 0 (p384.sl RY) =
    p384.mont p384.C.gy := by decide +kernel

theorem sat_point (hL : Weierstrass.Law Spec.P384.curve) :
    (mulCurve p384 "p384" "P-384").PointOk 0 (mulSatMem p384) :=
  mulSat_point p384_ok hL sat_x sat_y

theorem sat_pre (hL : Weierstrass.Law Spec.P384.curve) : (C.mulInRangeContract X86.abi 20).pre (mulSatState p384) :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      mulSatState]
    exact ⟨by decide, sat_consts, sat_point hL⟩)

/-- `vg_p384_mul` on x86. -/
theorem mul_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified X86.target mulP384 (C.mulInRangeContract X86.abi 20) :=
  VG.Proof.Ecdsa.X86.mul_verified (curve := "p384") (desc := "P-384") p384_ok hL mul_sp mul_ct (sat_pre hL)

end VG.Proof.Ecdsa.X86.P384.Mul
