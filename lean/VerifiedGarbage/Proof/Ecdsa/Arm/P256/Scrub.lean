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
`out` (`Proof/Ecdsa/Rfc6979/Arm/Scrub.lean`): each is registered followed
by a wipe of that stack (`Arm.Scrub.scrubRegFT`). The code's facts are
proved of `signCfg`, the configuration `cfgT` builds, written without the
group law that the curve's `RfcCurve` carries proofs of.
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

theorem frameOk_stackT : FrameOk stackT := by decide

/-- The configuration of signing's code, with `umaal` if `u`: the code is that
of `p256CombCurve`'s, whose other fields are proofs. -/
def signCfg (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := Proof.HmacTable.Arm.fnsOf vars
  w := 2 * Impl.Ecdsa.Arm.p256.n - (if Impl.Ecdsa.Arm.p256.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.p256.C.len
  big := false
  sh := 0
  n := Impl.Ecdsa.Arm.p256.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.p256.tries
  coreN := bif u then "vg_ecdsa_p256_sign_k" ++ "_umaal" else "vg_ecdsa_p256_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signP256CombU else Impl.Ecdsa.Arm.signP256Comb

theorem signCfg_code (u : Bool) :
    armStack (signCfg u).sign ≤ stackT ∧ tablesCall (signCfg u).sign [("hmac", tables vars)] = true := by
  cases u <;> lit_decide

/-- `vg_ecdsa_p256_sign`, given the group law. -/
def signReg (hC : Weierstrass.Law Spec.P256.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p256SignApi target :=
  Arm.Scrub.scrubRegFT {
      tables := [("hmac", tables vars)]
      code := signCodeT (p256CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
      verified := p256T_verified hC }
    (by exact (signCfg_code false).1) (by exact (signCfg_code false).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p256
      (p256CombCurve hC).coreConsts vars) rfl

/-- `vg_ecdsa_p256_sign_umaal`, given the group law. -/
def signUReg (hC : Weierstrass.Law Spec.P256.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p256SignApi target :=
  Arm.Scrub.scrubRegFT {
      suffix := "_umaal"
      tables := [("hmac", tables vars)]
      code := signCodeT (p256CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
      verified := p256UT_verified hC }
    (by exact (signCfg_code true).1) (by exact (signCfg_code true).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p256
      (p256CombCurveU hC).coreConsts vars) rfl

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

end VG.Proof.Ecdsa.Arm.Fn
