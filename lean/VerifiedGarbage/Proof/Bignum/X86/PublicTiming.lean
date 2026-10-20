module

public import VerifiedGarbage.Impl.Bignum.X86.PublicPower
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks

/-! # Constant-time arithmetic in the compact public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont.X86.Dynamic

theorem setup_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (setup n) contextSetupHint = some counterEndTaint :=
  exponent_check_seq taint (setupInverse_taint false (slot n 0) inverseOffset) (by rfl)
    (exponent_check_seq taint (one_check false n (slot n 4)) (by rfl)
      (powerTwo_check (modulus n) (slot n 2) (slot n 5) (128 * n)))

<<<<<<< HEAD
=======
theorem setup_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (setup n) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := contextSetupHint) ?_
  rw [setup_check]
  rfl

theorem exponentProduct_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint true) (exponentProduct n) productHint = some (rowTaint true) := by
  unfold exponentProduct multiply productHint
  exact exponent_check_seq taint (exponentMask_taint exponentOffset maskOffset) (by rfl)
    (exponent_check_seq taint (mul_check true _ _ _ _ _ _)
      (by rfl) (selectProduct_check (modulus n) (slot n 7) (slot n 5) maskOffset))

def publicBodyHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) productHint
    (.seq (workspaceTaint true) (mulHint true) (.block []))

def publicStepHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) publicBodyHint (.block [])

def publicExponentiateHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (mulHint false)
    (.seq (workspaceTaint false) (mulHint false)
      (.seq (workspaceTaint true) (.block [])
        (.seq (workspaceTaint false) (.loop (workspaceTaint true) publicStepHint) (mulHint false))))

theorem exponentBody_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint true) (exponentBody n) publicBodyHint = some (zeroTaint true) := by
  unfold exponentBody multiply publicBodyHint
  refine exponent_check_seq taint (exponentProduct_check n) (by rfl)
    (exponent_check_seq taint (mul_check true _ _ _ _ _ _) (by rfl) ?_)
  change taint.checkBlock (workspaceTaint true) (VG.Impl.Mont.X86.Dynamic.shiftExponent 2 exponentOffset) = _
  rw [shiftExponent_taint, ite_eq_right (by decide)]
  rfl

theorem exponentStep_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint true) (exponentStep n) publicStepHint = some counterEndTaint := by
  unfold exponentStep publicStepHint
  exact exponent_check_seq taint (exponentBody_check n) (by rfl) (by rfl)

theorem exponentiate_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (exponentiate n) publicExponentiateHint = some (rowTaint false) := by
  have loop : VG.Taint.check taint (workspaceTaint true) (.loop (exponentStep n) .ne)
      (.loop (workspaceTaint true) publicStepHint) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) (exponentStep n) publicStepHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [exponentStep_check n]
    rfl
  unfold exponentiate multiply publicExponentiateHint
  refine exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) ?_
  refine exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) ?_
  refine exponent_check_seq taint (u := workspaceTaint true) (by rfl) (by rfl) ?_
  exact exponent_check_seq taint loop (by rfl) (mul_check false _ _ _ _ _ _)

/-- Neither the modulus, base, exponent nor intermediate values need to be
public. Only the common workspace pointer is public on entry. -/
theorem exponentiate_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (exponentiate n) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := publicExponentiateHint) ?_
  rw [exponentiate_check n]
  rfl

def publicPowerHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) contextSetupHint publicExponentiateHint

theorem publicPower_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (publicPower n) publicPowerHint = some (rowTaint false) :=
  exponent_check_seq taint (setup_check n) (by rfl) (exponentiate_check n)

theorem publicPower_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (publicPower n) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := publicPowerHint) ?_
  rw [publicPower_check]
  rfl

>>>>>>> origin/claude/x86-rsa-crt-rt
end VG.Proof.Bignum.X86.PublicContext
