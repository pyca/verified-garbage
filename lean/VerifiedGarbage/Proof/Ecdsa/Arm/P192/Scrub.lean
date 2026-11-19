module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P192.Comb
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA over P192 on 32-bit ARM, without secret residue

`vg_ecdsa_p192_verify` and its `_umaal` variant keep the hash's working
values in a frame of 96 bytes and make no indirect call (the kernel's
evaluation of the code, with the literal of the verification core), and
their postcondition does not read the memory on return
(`Proof/Ecdsa/Verify/Arm/Scrub.lean`): each is registered followed by a
wipe of that stack (`Arm.Scrub.scrubRegF`).
`vg_ecdsa_p192_sign` and its `_umaal` variant call indirectly only the HMAC
functions of their table, from frames within the stack their contract
reserves, and their postcondition reads the memory on return only at
`out` (`Proof/Ecdsa/Rfc6979/Arm/Scrub.lean`): each is registered followed
by a wipe of that stack (`Arm.Scrub.scrubRegFT`). The code's facts are
proved of `signCfg`, the configuration `cfgT` builds, written without the
group law that the curve's `RfcCurve` carries proofs of.
All are then followed by instructions that set the registers a callee may
change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P192.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT p192CombCurve p192T_verified
  p192CombCurveU p192UT_verified stackT)
open VG.Proof.HmacTable.Arm (tables vars)

/-- Verification's code, with the comb, with `umaal` if `u`. -/
abbrev verifyCode (u : Bool) : Prog isa :=
  Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
    (bif u then Impl.Ecdsa.Arm.verifyP192CombU else Impl.Ecdsa.Arm.verifyP192Comb)

theorem verify_code : armStack (verifyCode false) ≤ 96 ∧ noIcall (verifyCode false) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP192Comb) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP192Comb) = true
  lit_decide

theorem verifyU_code : armStack (verifyCode true) ≤ 96 ∧ noIcall (verifyCode true) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP192CombU) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP192CombU) = true
  lit_decide

theorem frameOk_96 : FrameOk 96 := by decide

theorem frameOk_stackT : FrameOk stackT := by decide

/-- `vg_ecdsa_p192_verify`, given the group law. -/
def verifyReg (hC : Weierstrass.Law Spec.P192.curve) :
    Registration Spec.Ecdsa.P192.verifyHashApi target :=
  Arm.Scrub.scrubRegF {
      code := verifyCode false
      verified := Proof.Ecdsa.Verify.Arm.P192.verifyHash_verified hC }
    verify_code.1 verify_code.2 frameOk_96
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.P192.inst
      Impl.Weierstrass.Arm.p192CombConsts 96) rfl

/-- `vg_ecdsa_p192_verify_umaal`, given the group law. -/
def verifyUReg (hC : Weierstrass.Law Spec.P192.curve) :
    Registration Spec.Ecdsa.P192.verifyHashApi target :=
  Arm.Scrub.scrubRegF {
      suffix := "_umaal"
      code := verifyCode true
      verified := Proof.Ecdsa.Verify.Arm.P192.verifyHashU_verified hC }
    verifyU_code.1 verifyU_code.2 frameOk_96
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.P192.inst
      Impl.Weierstrass.Arm.p192CombConsts 96) rfl

/-- The configuration of signing's code, with `umaal` if `u`: the code is that
of `p192CombCurve`'s, whose other fields are proofs. -/
def signCfg (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := Proof.HmacTable.Arm.fnsOf vars
  w := 2 * Impl.Ecdsa.Arm.p192.n - (if Impl.Ecdsa.Arm.p192.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.p192.C.len
  big := false
  sh := 0
  n := Impl.Ecdsa.Arm.p192.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.p192.tries
  coreN := bif u then "vg_ecdsa_p192_sign_k" ++ "_umaal" else "vg_ecdsa_p192_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signP192CombU else Impl.Ecdsa.Arm.signP192Comb

theorem signCfg_code (u : Bool) :
    armStack (signCfg u).sign ≤ stackT ∧ tablesCall (signCfg u).sign [("hmac", tables vars)] = true := by
  cases u <;> lit_decide

/-- `vg_ecdsa_p192_sign`, given the group law. -/
def signReg (hC : Weierstrass.Law Spec.P192.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p192SignApi target :=
  Arm.Scrub.scrubRegFT {
      tables := [("hmac", tables vars)]
      code := signCodeT (p192CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      verified := p192T_verified hC }
    (by exact (signCfg_code false).1) (by exact (signCfg_code false).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p192
      (p192CombCurve hC).coreConsts vars) rfl

/-- `vg_ecdsa_p192_sign_umaal`, given the group law. -/
def signUReg (hC : Weierstrass.Law Spec.P192.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p192SignApi target :=
  Arm.Scrub.scrubRegFT {
      suffix := "_umaal"
      tables := [("hmac", tables vars)]
      code := signCodeT (p192CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      verified := p192UT_verified hC }
    (by exact (signCfg_code true).1) (by exact (signCfg_code true).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p192
      (p192CombCurveU hC).coreConsts vars) rfl

end VG.Proof.Ecdsa.Arm.P192.Scrub
