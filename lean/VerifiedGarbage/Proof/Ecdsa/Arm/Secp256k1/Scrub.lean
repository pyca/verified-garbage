module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA over Secp256k1 on 32-bit ARM, without secret residue

`vg_ecdsa_secp256k1_verify` and its `_umaal` variant keep the hash's working
values in a frame of 96 bytes and make no indirect call (the kernel's
evaluation of the code, with the literal of the verification core), and
their postcondition does not read the memory on return
(`Proof/Ecdsa/Verify/Arm/Scrub.lean`): each is emitted followed by a
wipe of that stack (`Impl.Ecdsa.Arm.Fn`), and `Fn` below has its theorem
(`Arm.Scrub.verifiedScrubbedF`).
`vg_ecdsa_secp256k1_sign` and its `_umaal` variant call indirectly only the HMAC
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

namespace VG.Proof.Ecdsa.Arm.Secp256k1.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT secp256k1CombCurve secp256k1T_verified
  secp256k1CombCurveU secp256k1UT_verified stackT)
open VG.Proof.HmacTable.Arm (tables vars)

/-- Verification's code, with the comb, with `umaal` if `u`. -/
abbrev verifyCode (u : Bool) : Prog isa :=
  Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
    (bif u then Impl.Ecdsa.Arm.verifySecp256k1CombU else Impl.Ecdsa.Arm.verifySecp256k1Comb)

theorem verify_code : armStack (verifyCode false) ≤ 96 ∧ noIcall (verifyCode false) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.Arm.verifySecp256k1Comb) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.Arm.verifySecp256k1Comb) = true
  lit_decide

theorem verifyU_code : armStack (verifyCode true) ≤ 96 ∧ noIcall (verifyCode true) = true := by
  show armStack (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.Arm.verifySecp256k1CombU) ≤ 96 ∧
    noIcall (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.Arm.verifySecp256k1CombU) = true
  lit_decide

theorem frameOk_96 : FrameOk 96 := by decide

theorem frameOk_stackT : FrameOk stackT := by decide

/-- The configuration of signing's code, with `umaal` if `u`: the code is that
of `secp256k1CombCurve`'s, whose other fields are proofs. -/
def signCfg (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := Proof.HmacTable.Arm.fnsOf vars
  w := 2 * Impl.Ecdsa.Arm.secp256k1.n - (if Impl.Ecdsa.Arm.secp256k1.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.secp256k1.C.len
  big := false
  sh := 0
  n := Impl.Ecdsa.Arm.secp256k1.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries
  coreN := bif u then "vg_ecdsa_secp256k1_sign_k" ++ "_umaal" else "vg_ecdsa_secp256k1_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signSecp256k1CombU else Impl.Ecdsa.Arm.signSecp256k1Comb

theorem signCfg_code (u : Bool) :
    armStack (signCfg u).sign ≤ stackT ∧ tablesCall (signCfg u).sign [("hmac", tables vars)] = true := by
  cases u <;> lit_decide

/-- `vg_ecdsa_secp256k1_sign`, given the group law. -/
def signReg (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi target :=
  Arm.Scrub.scrubRegFT {
      tables := [("hmac", tables vars)]
      code := signCodeT (secp256k1CombCurve hC) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      verified := secp256k1T_verified hC }
    (by exact (signCfg_code false).1) (by exact (signCfg_code false).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.secp256k1
      (secp256k1CombCurve hC).coreConsts vars) rfl

/-- `vg_ecdsa_secp256k1_sign_umaal`, given the group law. -/
def signUReg (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Registration Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi target :=
  Arm.Scrub.scrubRegFT {
      suffix := "_umaal"
      tables := [("hmac", tables vars)]
      code := signCodeT (secp256k1CombCurveU hC) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      verified := secp256k1UT_verified hC }
    (by exact (signCfg_code true).1) (by exact (signCfg_code true).2)
    frameOk_stackT
    (Proof.Ecdsa.Rfc6979.Arm.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.secp256k1
      (secp256k1CombCurveU hC).coreConsts vars) rfl

end VG.Proof.Ecdsa.Arm.Secp256k1.Scrub

namespace VG.Proof.Ecdsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdsa_secp256k1_verify`, given the group law. -/
theorem verifySecp256k1 (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifySecp256k1
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.secp256k1CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.Secp256k1.verifyHashApi)
    { code := Secp256k1.Scrub.verifyCode false
      verified := Proof.Ecdsa.Verify.Arm.Secp256k1.verifyHash_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.Secp256k1.inst
      Impl.Weierstrass.Arm.secp256k1CombConsts 96)
    (scrubSideF_of Secp256k1.Scrub.verify_code Secp256k1.Scrub.frameOk_96 _)

/-- `vg_ecdsa_secp256k1_verify_umaal`, given the group law. -/
theorem verifySecp256k1U (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.Arm.Fn.verifySecp256k1U
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract
        (abi.withConsts Impl.Weierstrass.Arm.secp256k1CombConsts) 96) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.Secp256k1.verifyHashApi)
    { code := Secp256k1.Scrub.verifyCode true
      verified := Proof.Ecdsa.Verify.Arm.Secp256k1.verifyHashU_verified hC }
    (Proof.Ecdsa.Verify.Arm.Scrub.verifyHashOut Spec.Ecdsa.Secp256k1.inst
      Impl.Weierstrass.Arm.secp256k1CombConsts 96)
    (scrubSideF_of Secp256k1.Scrub.verifyU_code Secp256k1.Scrub.frameOk_96 _)

end VG.Proof.Ecdsa.Arm.Fn
