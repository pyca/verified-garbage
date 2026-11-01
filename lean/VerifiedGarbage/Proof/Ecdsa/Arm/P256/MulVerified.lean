module

public import VerifiedGarbage.Proof.Ecdsa.Arm.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P256.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.MulLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P256.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.MulLit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# `vg_p256_mul` on 32-bit ARM: `Verified`

`mul_verified` for P-256 (`p256_ok`), with the function's constant time by
taint tracking (only the pointer, in `r0`, public: every address is `r12`
plus a constant or a counter, and the only branches are on loop counters)
and a state satisfying the precondition (`mulSatState`: the constants and `G`
in Montgomery's form at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P256.Mul

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof

/-- P-256's curve of `Proof/Weierstrass/MulContract.lean`: the one its code has. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p256

theorem C_eq : C = mulCurve p256 "p256" "P-256" := rfl

theorem mul_ct : ConstantTime isa (mulArm C).pre (mulArm C).pub mulP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.2) (by native_taint_decide)

theorem sat_consts : C.ConstsOk 0x1000 (mulSatMem p256) := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_pre (hL : Weierstrass.Law Spec.P256.curve) : (C.mulInRangeContract Arm.abi).pre (mulSatState p256) :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, Arm.abi, Arm.argRegs, Arm.Loc.val, mulSatState]
    exact ⟨by decide, sat_consts, mulSat_point (curve := "p256") (desc := "P-256") (saved := 1) p256_ok hL
      (by decide +kernel) (by decide +kernel)⟩)

/-- `vg_p256_mul` on 32-bit ARM. -/
theorem mul_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target mulP256 (C.mulInRangeContract Arm.abi) :=
  VG.Proof.Ecdsa.Arm.mul_verified (curve := "p256") (desc := "P-256") (saved := 1) p256_ok hL mul_ct
    ⟨_, sat_pre hL⟩

end VG.Proof.Ecdsa.Arm.P256.Mul
