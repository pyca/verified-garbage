module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdsa.P521.ArmFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Comb
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA over P521 on 32-bit ARM, without secret residue

`vg_ecdsa_p521_verify` and its `_umaal` variant keep the hash's working
values in a frame of 96 bytes and make no indirect call (the kernel's
evaluation of the code, with the literal of the verification core), and
their postcondition does not read the memory on return
(`Proof/Ecdsa/Verify/Arm/Scrub.lean`): each is emitted followed by a
wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its theorem
(`Arm.Scrub.verifiedScrubbedF`).
`vg_ecdsa_p521_sign` and its `_umaal` variant call indirectly only the HMAC
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

namespace VG.Proof.Ecdsa.Arm.P521.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT p521CombCurve p521T_verified
  p521CombCurveU p521UT_verified stackT)
open VG.Proof.HmacTable.Arm (tables vars)

/-- Verification's code, with the comb, with `umaal` if `u`. -/
abbrev verifyCode (u : Bool) : Prog isa :=
  Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
    (bif u then Impl.Ecdsa.Arm.verifyP521CombU else Impl.Ecdsa.Arm.verifyP521Comb)

theorem verify_code : armStack (verifyCode false) ≤ 96 ∧ noIcall (verifyCode false) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Arm.verifyP521Comb) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Arm.verifyP521Comb) = true
  lit_decide

theorem verifyU_code : armStack (verifyCode true) ≤ 96 ∧ noIcall (verifyCode true) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Arm.verifyP521CombU) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Arm.verifyP521CombU) = true
  lit_decide

theorem frameOk_96 : FrameOk 96 := by decide

theorem frameOk_stackT : FrameOk stackT := by decide

/-- The configuration of signing's code, with `umaal` if `u`: the code is that
of `p521CombCurve`'s, whose other fields are proofs. -/
def signCfg (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := Proof.HmacTable.Arm.fnsOf vars
  w := 2 * Impl.Ecdsa.Arm.p521.n - (if Impl.Ecdsa.Arm.p521.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.p521.C.len
  big := true
  sh := 7
  n := Impl.Ecdsa.Arm.p521.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.p521.tries
  coreN := bif u then "vg_ecdsa_p521_sign_k" ++ "_umaal" else "vg_ecdsa_p521_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signP521CombU else Impl.Ecdsa.Arm.signP521Comb

theorem signCfg_code (u : Bool) :
    armStack (signCfg u).sign ≤ stackT ∧ tablesCall (signCfg u).sign [("hmac", tables vars)] = true := by
  cases u <;> lit_decide

/-- `vg_ecdsa_p521_sign`, given the group law. -/
def signReg (hC : Weierstrass.Law Spec.P521.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p521SignApi target :=
  Arm.Scrub.scrubRegFT {
      tables := [("hmac", tables vars)]
      code := signCodeT (p521CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
      verified := p521T_verified hC }
    (by exact (signCfg_code false).1) (by exact (signCfg_code false).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p521
      (p521CombCurve hC).coreConsts vars) rfl

/-- `vg_ecdsa_p521_sign_umaal`, given the group law. -/
def signUReg (hC : Weierstrass.Law Spec.P521.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p521SignApi target :=
  Arm.Scrub.scrubRegFT {
      suffix := "_umaal"
      tables := [("hmac", tables vars)]
      code := signCodeT (p521CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
      verified := p521UT_verified hC }
    (by exact (signCfg_code true).1) (by exact (signCfg_code true).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p521
      (p521CombCurveU hC).coreConsts vars) rfl

end VG.Proof.Ecdsa.Arm.P521.Scrub

namespace VG.Proof.Ecdsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdsa_p521_verify`, given the group law. -/
theorem verifyP521 (hC : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyP521
      (Spec.Ecdsa.P521.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.p521CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.P521.verifyHashApi)
    { code := P521.Scrub.verifyCode false
      verified := Proof.Ecdsa.Verify.Arm.P521.verifyHash_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.P521.inst
      Impl.Weierstrass.Arm.p521CombConsts 96)
    (scrubSideF_of P521.Scrub.verify_code P521.Scrub.frameOk_96 _)

/-- `vg_ecdsa_p521_verify_umaal`, given the group law. -/
theorem verifyP521U (hC : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifyP521U
      (Spec.Ecdsa.P521.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.p521CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.P521.verifyHashApi)
    { code := P521.Scrub.verifyCode true
      verified := Proof.Ecdsa.Verify.Arm.P521.verifyHashU_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.P521.inst
      Impl.Weierstrass.Arm.p521CombConsts 96)
    (scrubSideF_of P521.Scrub.verifyU_code P521.Scrub.frameOk_96 _)

end VG.Proof.Ecdsa.Arm.Fn
