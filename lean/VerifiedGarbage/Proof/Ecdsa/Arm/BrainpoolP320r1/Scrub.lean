module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.ArmFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP320r1.Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP320r1Comb
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.CombLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.ArmFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP320r1.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP320r1Comb
meta import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
meta import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDSA over brainpoolP320r1 on 32-bit ARM, without secret residue

`vg_ecdsa_brainpoolp320r1_verify` keeps the hash's working values in a frame
of 96 bytes and makes no indirect call, and its postcondition does not read
the memory on return (`Proof/Ecdsa/Verify/Arm/Scrub.lean`): it is emitted
followed by a wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its
theorem (`Arm.Scrub.verifiedScrubbedF`).
`vg_ecdsa_brainpoolp320r1_sign` calls indirectly only the HMAC functions of
its table, from frames within the stack its contract reserves, and its
postcondition reads the memory on return only at `out`
(`Proof/Ecdsa/Rfc6979/Arm/Scrub.lean`): it is registered followed by a wipe of
that stack (`Arm.Scrub.scrubRegFT`). Both are then followed by instructions
that set the registers a callee may change, but the result, and the flags to
constants; with either multiplication of the field.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP320r1.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT brainpoolp320r1CombCurve brainpoolp320r1T_verified
  brainpoolp320r1CombCurveU brainpoolp320r1UT_verified stackT)
open VG.Proof.HmacTable.Arm (tables vars)

/-- Verification's code, with the comb, calling `vg_brainpoolp320r1_mul_public` with `umaal` if `u`. -/
abbrev verifyCode (u : Bool) : Prog isa :=
  Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
    (Impl.Ecdsa.Arm.verifyBrainpoolP320r1CombWith u)

theorem verify_noIcall : noIcall (verifyCode false) = true := by
  show noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
    Impl.Ecdsa.Arm.verifyBrainpoolP320r1Comb) = true
  lit_decide

theorem verifyU_noIcall : noIcall (verifyCode true) = true := by
  show noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
    Impl.Ecdsa.Arm.verifyBrainpoolP320r1CombU) = true
  lit_decide

theorem verify_armStack : armStack (verifyCode false) ≤ 96 := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
    Impl.Ecdsa.Arm.verifyBrainpoolP320r1Comb) ≤ 96
  lit_decide

theorem verifyU_armStack : armStack (verifyCode true) ≤ 96 := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
    Impl.Ecdsa.Arm.verifyBrainpoolP320r1CombU) ≤ 96
  lit_decide

theorem frameOk_96 : FrameOk 96 := by decide

theorem frameOk_stackT : FrameOk stackT := by decide

/-- The configuration of signing's code, the comb's core calling
`vg_brainpoolp320r1_mul` with `umaal` if `u`: the code is that of
`brainpoolp320r1CombCurve`'s (`signCode_eq`), whose other fields are proofs. -/
def signCfg (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := Proof.HmacTable.Arm.fnsOf vars
  w := 2 * Impl.Ecdsa.Arm.brainpoolp320r1.n - (if Impl.Ecdsa.Arm.brainpoolp320r1.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.brainpoolp320r1.C.len
  big := false
  sh := 0
  n := Impl.Ecdsa.Arm.brainpoolp320r1.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries
  coreN := bif u then "vg_ecdsa_brainpoolp320r1_sign_k" ++ "_umaal" else "vg_ecdsa_brainpoolp320r1_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signBrainpoolP320r1CombU else Impl.Ecdsa.Arm.signBrainpoolP320r1Comb

theorem signCode_eq (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    signCodeT (brainpoolp320r1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars =
      (signCfg false).sign := rfl

theorem signCodeU_eq (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    signCodeT (brainpoolp320r1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars =
      (signCfg true).sign := rfl

theorem signCfg_tablesCall (u : Bool) : tablesCall (signCfg u).sign [("hmac", tables vars)] = true := by
  cases u <;> lit_decide

theorem signCfg_armStack (u : Bool) : armStack (signCfg u).sign ≤ stackT := by
  cases u <;> lit_decide

theorem sign_tablesCall (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    tablesCall (signCodeT (brainpoolp320r1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars)
      [("hmac", tables vars)] = true := by
  rw [signCode_eq]; exact signCfg_tablesCall false

theorem signU_tablesCall (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    tablesCall (signCodeT (brainpoolp320r1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars)
      [("hmac", tables vars)] = true := by
  rw [signCodeU_eq]; exact signCfg_tablesCall true

theorem sign_armStack (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    armStack (signCodeT (brainpoolp320r1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars) ≤
      stackT := by
  rw [signCode_eq]; exact signCfg_armStack false

theorem signU_armStack (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    armStack (signCodeT (brainpoolp320r1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars) ≤
      stackT := by
  rw [signCodeU_eq]; exact signCfg_armStack true

/-- `vg_ecdsa_brainpoolp320r1_sign`, given the group law. -/
def signReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi target :=
  Arm.Scrub.scrubRegFT {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp320r1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars
      verified := brainpoolp320r1T_verified hC }
    (sign_armStack hC) (sign_tablesCall hC) frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1
      (brainpoolp320r1CombCurve hC).coreConsts vars) rfl

/-- `vg_ecdsa_brainpoolp320r1_sign_umaal`, given the group law. -/
def signUReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi target :=
  Arm.Scrub.scrubRegFT {
      suffix := "_umaal"
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp320r1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars
      verified := brainpoolp320r1UT_verified hC }
    (signU_armStack hC) (signU_tablesCall hC) frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1
      (brainpoolp320r1CombCurveU hC).coreConsts vars) rfl

end VG.Proof.Ecdsa.Arm.BrainpoolP320r1.Scrub

namespace VG.Proof.Ecdsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdsa_brainpoolp320r1_verify`, given the group law. -/
theorem verifyBrainpoolP320r1 (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyBrainpoolP320r1
      (Spec.Ecdsa.BrainpoolP320r1.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.brainpoolp320r1CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.BrainpoolP320r1.verifyHashApi)
    { code := BrainpoolP320r1.Scrub.verifyCode false
      verified := Proof.Ecdsa.Verify.Arm.BrainpoolP320r1.verifyHash_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.BrainpoolP320r1.inst
      Impl.Weierstrass.Arm.brainpoolp320r1CombConsts 96)
    (scrubSideF_of ⟨BrainpoolP320r1.Scrub.verify_armStack, BrainpoolP320r1.Scrub.verify_noIcall⟩
      BrainpoolP320r1.Scrub.frameOk_96 _)

/-- `vg_ecdsa_brainpoolp320r1_verify_umaal`, given the group law. -/
theorem verifyBrainpoolP320r1U (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyBrainpoolP320r1U
      (Spec.Ecdsa.BrainpoolP320r1.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.brainpoolp320r1CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.BrainpoolP320r1.verifyHashApi)
    { code := BrainpoolP320r1.Scrub.verifyCode true
      verified := Proof.Ecdsa.Verify.Arm.BrainpoolP320r1.verifyHashU_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.BrainpoolP320r1.inst
      Impl.Weierstrass.Arm.brainpoolp320r1CombConsts 96)
    (scrubSideF_of ⟨BrainpoolP320r1.Scrub.verifyU_armStack, BrainpoolP320r1.Scrub.verifyU_noIcall⟩
      BrainpoolP320r1.Scrub.frameOk_96 _)

end VG.Proof.Ecdsa.Arm.Fn
