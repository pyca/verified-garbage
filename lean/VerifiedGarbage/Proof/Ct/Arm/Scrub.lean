module

public import VerifiedGarbage.Proof.Ct.Arm
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ct.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Constant-time comparison on ARMv7, without secret residue

`vg_ct_eq` saves `r4` in a frame, so its cleanup zeroes the stack its
contract reserves on return (`Impl.Ct.Arm.Fn.eq`, `Arm.Scrub.scrubF`), and
`Fn.eq` below states that it returns without secret residue
(`Arm.Scrub.verifiedScrubbedF`). Its proof is with the 4 bytes of that
frame, which is no frame size of the model (`FrameOk`), so its contract
reserves 8 (`Arm.Scrub.Verified.stack_le`). Its
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

theorem eq_codeOkArm : CodeOk Impl.Ct.Arm.eq 8 := ⟨eq_armStackArm, eq_noIcallArm⟩

end VG.Proof.Ct.Arm.Scrub

namespace VG.Proof.Ct.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ct_eq`. -/
theorem eq : VerifiedScrubbed target Impl.Ct.Arm.Fn.eq (Spec.Ct.eqContract abi 8) 32 :=
  verifiedScrubbedF (api := Spec.Ct.eqApi) { code := Impl.Ct.Arm.eq, verified := Scrub.verified8 }
    Scrub.eqOutArm (scrubSideF_of Scrub.eq_codeOkArm (by decide) _)

end VG.Proof.Ct.Arm.Fn
