import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
import VerifiedGarbage.Proof.Weierstrass.Arm.MontP192
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Spec.P192
import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Spec.P384

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: the curves

Each curve of `Spec.Weierstrass.Point.curves` is one the functions support:
its prime's Montgomery functions (`ModOk`), and the functions' constant time
by taint tracking, from the pointer's register (`r0`) public. Fermat's
little theorem in `Fin p` follows from the curve's group law
(`fermat_of_law`), which the registration files supply.
-/

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Point VG.Proof.Weierstrass.Arm.Mont Spec.Weierstrass.Point

theorem pub_agree {C : Curve} {dbl : Bool} {s₁ s₂ : State} (h : (sumArm C dbl).pub s₁ s₂) :
    ∀ r ∈ [Reg.r0], s₁.gpr r = s₂.gpr r := by
  intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.2

/-- Fermat's little theorem in `Fe C`: `1 = (1 Z) Z^(p-2)` (`Law.x_eq` for
the representative `(Z : 0 : Z)` of the pair `(1, 0)`). -/
theorem fermat_of_law {CW : Spec.Weierstrass.Curve} (hL : VG.Proof.Weierstrass.Law CW) : Fermat CW.p :=
  fun z hz => by
    rw [VG.Proof.Weierstrass.pow_eq_npow]
    have h : VG.Proof.Weierstrass.Rep CW (1 * z) (0 * z) z (.affine 1 0) := ⟨hz, rfl, rfl⟩
    have e := hL.x_eq h
    rw [e]; grind

theorem p192_add_ct : ConstantTime isa (sumArm p192 false).pre (sumArm p192 false).pub (fn (modP p192) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p192_double_ct : ConstantTime isa (sumArm p192 true).pre (sumArm p192 true).pub (fn (modP p192) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p192_add_verified (hF : Fermat p192.p) : Verified Arm.target (pointAdd p192) (p192.addContract Arm.abi) :=
  sum_verified p192 Mont.p192p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false p192_add_ct

theorem p192_double_verified (hF : Fermat p192.p) :
    Verified Arm.target (pointDouble p192) (p192.doubleContract Arm.abi) :=
  sum_verified p192 Mont.p192p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true p192_double_ct

theorem p224_add_ct : ConstantTime isa (sumArm p224 false).pre (sumArm p224 false).pub (fn (modP p224) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p224_double_ct : ConstantTime isa (sumArm p224 true).pre (sumArm p224 true).pub (fn (modP p224) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p224_add_verified (hF : Fermat p224.p) : Verified Arm.target (pointAdd p224) (p224.addContract Arm.abi) :=
  sum_verified p224 Mont.p224p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false p224_add_ct

theorem p224_double_verified (hF : Fermat p224.p) :
    Verified Arm.target (pointDouble p224) (p224.doubleContract Arm.abi) :=
  sum_verified p224 Mont.p224p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true p224_double_ct

theorem p256_add_ct : ConstantTime isa (sumArm p256 false).pre (sumArm p256 false).pub (fn (modP p256) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p256_double_ct : ConstantTime isa (sumArm p256 true).pre (sumArm p256 true).pub (fn (modP p256) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p256_add_verified (hF : Fermat p256.p) : Verified Arm.target (pointAdd p256) (p256.addContract Arm.abi) :=
  sum_verified p256 Mont.p256p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false p256_add_ct

theorem p256_double_verified (hF : Fermat p256.p) :
    Verified Arm.target (pointDouble p256) (p256.doubleContract Arm.abi) :=
  sum_verified p256 Mont.p256p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true p256_double_ct

theorem p384_add_ct : ConstantTime isa (sumArm p384 false).pre (sumArm p384 false).pub (fn (modP p384) false) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p384_double_ct : ConstantTime isa (sumArm p384 true).pre (sumArm p384 true).pub (fn (modP p384) true) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (pub_agree hp)) (by taint_decide)

theorem p384_add_verified (hF : Fermat p384.p) : Verified Arm.target (pointAdd p384) (p384.addContract Arm.abi) :=
  sum_verified p384 Mont.p384p_ok (by decide) (by decide +kernel) (by decide +kernel) hF false p384_add_ct

theorem p384_double_verified (hF : Fermat p384.p) :
    Verified Arm.target (pointDouble p384) (p384.doubleContract Arm.abi) :=
  sum_verified p384 Mont.p384p_ok (by decide) (by decide +kernel) (by decide +kernel) hF true p384_double_ct

end VG.Proof.Weierstrass.Arm.Point
