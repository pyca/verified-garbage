module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P192.Comb
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scrub
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
All are then followed by instructions that set the registers a callee may
change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P192.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

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

end VG.Proof.Ecdsa.Arm.P192.Scrub
