module

public import VerifiedGarbage.Proof.Ct.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ct.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Constant-time comparison on ARMv7, without secret residue

`vg_ct_eq` saves `r4` in a frame, so it is registered with the stack its
contract reserves zeroed on return (`Arm.Scrub.scrubRegF`). Its proof is
with the 4 bytes of that frame, which is no frame size of the model
(`FrameOk`), so it is registered with 8 (`Arm.Scrub.Verified.stack_le`). Its
postcondition reads no memory on return (`Arm.Scrub.PostOut`): it writes
none, as on the other targets (`Proof/Ct/RISCV64Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Ct.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

theorem sat8 : ∃ s, (Spec.Ct.eqContract abi 8).pre s := by
  sig_implies_sat [Spec.Ct.eqContract, Spec.Ct.eqSig, abi, argRegs, reduceClassify, Loc.val] [sat] using sat

theorem verified8 : Verified target Impl.Ct.Arm.eq (Spec.Ct.eqContract abi 8) :=
  Verified.stack_le (by decide) verified sat8

theorem eqOutArm : PostOut (Spec.Ct.eqContract abi 8) (Spec.Ct.eqSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨a, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨bl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

theorem eq_noIcallArm : noIcall Impl.Ct.Arm.eq = true := by lit_decide

theorem eq_armStackArm : armStack Impl.Ct.Arm.eq ≤ 8 := by lit_decide

/-- `Spec.Ct.eqApi`, with its stack wiped on return. -/
def eqRegArm : Registration Spec.Ct.eqApi target :=
  scrubRegF { code := Impl.Ct.Arm.eq, verified := verified8 }
    eq_armStackArm eq_noIcallArm (by decide) eqOutArm rfl

end VG.Proof.Ct.Arm.Scrub
