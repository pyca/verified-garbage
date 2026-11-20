module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Comb
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA over BrainpoolP512r1 on 32-bit ARM, without secret residue

`vg_ecdsa_brainpoolp512r1_verify` and its `_umaal` variant keep the hash's working
values in a frame of 96 bytes and make no indirect call (the kernel's
evaluation of the code, with the literal of the verification core), and
their postcondition does not read the memory on return
(`Proof/Ecdsa/Verify/Arm/Scrub.lean`): each is emitted followed by a
wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its theorem
(`Arm.Scrub.verifiedScrubbedAll`).
`vg_ecdsa_brainpoolp512r1_sign` and its `_umaal` variant call indirectly only the HMAC
functions of their table, from frames within the stack their contract
reserves, and their postcondition reads the memory on return only at
`out` (`Proof/Ecdsa/Rfc6979/Arm/Scrub.lean`): each is emitted followed
by a wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its theorem
(`Arm.Scrub.verifiedScrubbedAll`). What the cleanup needs of
signing's code follows, for any curve, from `Rfc6979.Arm.Scrub.sign_okT` and
from what the core states of its own code (`signCore_ok`, by `lit_decide`);
`signCode_eq` is that the code `cfgT` builds is that of
`Impl.Ecdsa.Arm.Fn.signCfgBrainpoolP512r1`, written without the group law that the curve's
`RfcCurve` carries proofs of.
All are then followed by instructions that set the registers a callee may
change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT brainpoolp512r1CombCurve brainpoolp512r1T_verified
  brainpoolp512r1CombCurveU brainpoolp512r1UT_verified stackT)
open VG.Proof.HmacTable.Arm (tables vars)

/-- Verification's code, with the comb, with `umaal` if `u`. -/
abbrev verifyCode (u : Bool) : Prog isa :=
  Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
    (bif u then Impl.Ecdsa.Arm.verifyBrainpoolP512r1CombU else Impl.Ecdsa.Arm.verifyBrainpoolP512r1Comb)

theorem verify_code : armStack (verifyCode false) ≤ 96 ∧ noIcall (verifyCode false) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP512r1Comb) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP512r1Comb) = true
  lit_decide

theorem verifyU_code : armStack (verifyCode true) ≤ 96 ∧ noIcall (verifyCode true) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP512r1CombU) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP512r1CombU) = true
  lit_decide

theorem frameOk_96 : FrameOk 96 := by decide

theorem signCore_ok : CodeOk Impl.Ecdsa.Arm.signBrainpoolP512r1Comb 16 := by lit_decide

theorem signCoreU_ok : CodeOk Impl.Ecdsa.Arm.signBrainpoolP512r1CombU 16 := by lit_decide

theorem signCode_eq (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    signCodeT (brainpoolp512r1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars =
      (Impl.Ecdsa.Arm.Fn.signCfgBrainpoolP512r1 (Proof.HmacTable.Arm.fnsOf vars) false).sign := rfl

theorem signCodeU_eq (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    signCodeT (brainpoolp512r1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars =
      (Impl.Ecdsa.Arm.Fn.signCfgBrainpoolP512r1 (Proof.HmacTable.Arm.fnsOf vars) true).sign := rfl

end VG.Proof.Ecdsa.Arm.BrainpoolP512r1.Scrub

namespace VG.Proof.Ecdsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdsa_brainpoolp512r1_verify`, given the group law. -/
theorem verifyBrainpoolP512r1 (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyBrainpoolP512r1
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.brainpoolp512r1CombConsts) 96) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.BrainpoolP512r1.verifyHashApi)
    { code := BrainpoolP512r1.Scrub.verifyCode false
      verified := Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.verifyHash_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.BrainpoolP512r1.inst
      Impl.Weierstrass.Arm.brainpoolp512r1CombConsts 96)
    (scrubSideF_of BrainpoolP512r1.Scrub.verify_code BrainpoolP512r1.Scrub.frameOk_96 _)

/-- `vg_ecdsa_brainpoolp512r1_verify_umaal`, given the group law. -/
theorem verifyBrainpoolP512r1U (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyBrainpoolP512r1U
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.brainpoolp512r1CombConsts) 96) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.BrainpoolP512r1.verifyHashApi)
    { code := BrainpoolP512r1.Scrub.verifyCode true
      verified := Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.verifyHashU_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.BrainpoolP512r1.inst
      Impl.Weierstrass.Arm.brainpoolp512r1CombConsts 96)
    (scrubSideF_of BrainpoolP512r1.Scrub.verifyU_code BrainpoolP512r1.Scrub.frameOk_96 _)


/-- `vg_ecdsa_brainpoolp512r1_sign`, given the group law. -/
theorem signBrainpoolP512r1 (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target (Impl.Ecdsa.Arm.Fn.signBrainpoolP512r1 (HmacTable.Arm.fnsOf HmacTable.Arm.vars))
      (Ecdsa.Rfc6979.Arm.specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1
        (Ecdsa.Rfc6979.Arm.brainpoolp512r1CombCurve hC).coreConsts HmacTable.Arm.vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi)
    { tables := [("hmac", HmacTable.Arm.tables HmacTable.Arm.vars)]
      code := Ecdsa.Rfc6979.Arm.signCodeT (Ecdsa.Rfc6979.Arm.brainpoolp512r1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries HmacTable.Arm.vars
      verified := Ecdsa.Rfc6979.Arm.brainpoolp512r1T_verified hC }
    (Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1
      (Ecdsa.Rfc6979.Arm.brainpoolp512r1CombCurve hC).coreConsts HmacTable.Arm.vars)
    (Ecdsa.Rfc6979.Arm.Scrub.sign_side_of (BrainpoolP512r1.Scrub.signCode_eq hC) rfl BrainpoolP512r1.Scrub.signCore_ok)

/-- `vg_ecdsa_brainpoolp512r1_sign_umaal`, given the group law. -/
theorem signBrainpoolP512r1U (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target (Impl.Ecdsa.Arm.Fn.signBrainpoolP512r1U (HmacTable.Arm.fnsOf HmacTable.Arm.vars))
      (Ecdsa.Rfc6979.Arm.specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1
        (Ecdsa.Rfc6979.Arm.brainpoolp512r1CombCurveU hC).coreConsts HmacTable.Arm.vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi)
    { tables := [("hmac", HmacTable.Arm.tables HmacTable.Arm.vars)]
      code := Ecdsa.Rfc6979.Arm.signCodeT (Ecdsa.Rfc6979.Arm.brainpoolp512r1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries HmacTable.Arm.vars
      verified := Ecdsa.Rfc6979.Arm.brainpoolp512r1UT_verified hC }
    (Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1
      (Ecdsa.Rfc6979.Arm.brainpoolp512r1CombCurveU hC).coreConsts HmacTable.Arm.vars)
    (Ecdsa.Rfc6979.Arm.Scrub.sign_side_of (BrainpoolP512r1.Scrub.signCodeU_eq hC) rfl BrainpoolP512r1.Scrub.signCoreU_ok)

end VG.Proof.Ecdsa.Arm.Fn
