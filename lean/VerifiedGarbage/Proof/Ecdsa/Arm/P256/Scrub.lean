module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdsa.P256.ArmFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA over P256 on 32-bit ARM, without secret residue

`vg_ecdsa_p256_verify` and its `_umaal` variant keep the hash's working
values in a frame of 96 bytes and make no indirect call (the kernel's
evaluation of the code, with the literal of the verification core), and
their postcondition does not read the memory on return
(`Proof/Ecdsa/Verify/Arm/Scrub.lean`): each is emitted followed by a
wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its theorem
(`Arm.Scrub.verifiedScrubbedF`).
`vg_ecdsa_p256_sign` and its `_umaal` variant call indirectly only the HMAC
functions of their table, from frames within the stack their contract
reserves, and their postcondition reads the memory on return only at
`out` (`Proof/Ecdsa/Rfc6979/Arm/Scrub.lean`): each is emitted followed
by a wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its theorem
(`Arm.Scrub.verifiedScrubbedF`). What the cleanup needs of
signing's code follows, for any curve, from `Rfc6979.Arm.Scrub.sign_okT` and
from what the core states of its own code (`signCore_ok`, by `lit_decide`);
`signCode_eq` is that the code `cfgT` builds is that of
`Impl.Ecdsa.Arm.Fn.signCfgP256`, written without the group law that the curve's
`RfcCurve` carries proofs of.
All are then followed by instructions that set the registers a callee may
change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P256.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT p256CombCurve p256T_verified
  p256CombCurveU p256UT_verified stackT)
open VG.Proof.HmacTable.Arm (tables vars)

/-- Verification's code, with the comb, with `umaal` if `u`. -/
abbrev verifyCode (u : Bool) : Prog isa :=
  Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
    (bif u then Impl.Ecdsa.Arm.verifyP256CombU else Impl.Ecdsa.Arm.verifyP256Comb)

theorem verify_code : armStack (verifyCode false) ≤ 96 ∧ noIcall (verifyCode false) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP256Comb) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP256Comb) = true
  lit_decide

theorem verifyU_code : armStack (verifyCode true) ≤ 96 ∧ noIcall (verifyCode true) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP256CombU) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP256CombU) = true
  lit_decide

theorem frameOk_96 : FrameOk 96 := by decide

theorem signCore_ok : CodeOk Impl.Ecdsa.Arm.signP256Comb 16 := by lit_decide

theorem signCoreU_ok : CodeOk Impl.Ecdsa.Arm.signP256CombU 16 := by lit_decide

theorem signCode_eq (hC : Weierstrass.Law Spec.P256.curve) :
    signCodeT (p256CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars =
      (Impl.Ecdsa.Arm.Fn.signCfgP256 (Proof.HmacTable.Arm.fnsOf vars) false).sign := rfl

theorem signCodeU_eq (hC : Weierstrass.Law Spec.P256.curve) :
    signCodeT (p256CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars =
      (Impl.Ecdsa.Arm.Fn.signCfgP256 (Proof.HmacTable.Arm.fnsOf vars) true).sign := rfl

end VG.Proof.Ecdsa.Arm.P256.Scrub

namespace VG.Proof.Ecdsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdsa_p256_verify`, given the group law. -/
theorem verifyP256 (hC : Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyP256
      (Spec.Ecdsa.P256.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.p256CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.P256.verifyHashApi)
    { code := P256.Scrub.verifyCode false
      verified := Proof.Ecdsa.Verify.Arm.P256.verifyHash_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.P256.inst
      Impl.Weierstrass.Arm.p256CombConsts 96)
    (scrubSideF_of P256.Scrub.verify_code P256.Scrub.frameOk_96 _)

/-- `vg_ecdsa_p256_verify_umaal`, given the group law. -/
theorem verifyP256U (hC : Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyP256U
      (Spec.Ecdsa.P256.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.p256CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.P256.verifyHashApi)
    { code := P256.Scrub.verifyCode true
      verified := Proof.Ecdsa.Verify.Arm.P256.verifyHashU_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.P256.inst
      Impl.Weierstrass.Arm.p256CombConsts 96)
    (scrubSideF_of P256.Scrub.verifyU_code P256.Scrub.frameOk_96 _)


/-- `vg_ecdsa_p256_sign`, given the group law. -/
theorem signP256 (hC : Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target (Impl.Ecdsa.Arm.Fn.signP256 (HmacTable.Arm.fnsOf HmacTable.Arm.vars))
      (Ecdsa.Rfc6979.Arm.specK Spec.Ecdsa.Rfc6979.Curves.p256
        (Ecdsa.Rfc6979.Arm.p256CombCurve hC).coreConsts HmacTable.Arm.vars) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.Rfc6979.Curves.p256SignApi)
    { tables := [("hmac", HmacTable.Arm.tables HmacTable.Arm.vars)]
      code := Ecdsa.Rfc6979.Arm.signCodeT (Ecdsa.Rfc6979.Arm.p256CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.p256.tries HmacTable.Arm.vars
      verified := Ecdsa.Rfc6979.Arm.p256T_verified hC }
    (Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p256
      (Ecdsa.Rfc6979.Arm.p256CombCurve hC).coreConsts HmacTable.Arm.vars)
    (Ecdsa.Rfc6979.Arm.Scrub.sign_side_of (P256.Scrub.signCode_eq hC) rfl P256.Scrub.signCore_ok)

/-- `vg_ecdsa_p256_sign_umaal`, given the group law. -/
theorem signP256U (hC : Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target (Impl.Ecdsa.Arm.Fn.signP256U (HmacTable.Arm.fnsOf HmacTable.Arm.vars))
      (Ecdsa.Rfc6979.Arm.specK Spec.Ecdsa.Rfc6979.Curves.p256
        (Ecdsa.Rfc6979.Arm.p256CombCurveU hC).coreConsts HmacTable.Arm.vars) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.Rfc6979.Curves.p256SignApi)
    { tables := [("hmac", HmacTable.Arm.tables HmacTable.Arm.vars)]
      code := Ecdsa.Rfc6979.Arm.signCodeT (Ecdsa.Rfc6979.Arm.p256CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.p256.tries HmacTable.Arm.vars
      verified := Ecdsa.Rfc6979.Arm.p256UT_verified hC }
    (Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p256
      (Ecdsa.Rfc6979.Arm.p256CombCurveU hC).coreConsts HmacTable.Arm.vars)
    (Ecdsa.Rfc6979.Arm.Scrub.sign_side_of (P256.Scrub.signCodeU_eq hC) rfl P256.Scrub.signCoreU_ok)

end VG.Proof.Ecdsa.Arm.Fn
