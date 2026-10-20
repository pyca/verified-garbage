module
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks

/-! # Secret-independent branches and addresses for modular exponentiation -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem exponent_check_seq {M : ISA} (A : VG.Taint M) {τ mid u v : A.T}
    {a b : Prog M} {ha hb : VG.Taint.Hint A.T}
    (h₁ : VG.Taint.check A τ a ha = some u) (hl : A.le mid u = true)
    (h₂ : VG.Taint.check A mid b hb = some v) :
    VG.Taint.check A τ (.seq a b) (.seq mid ha hb) = some v := by
  change (VG.Taint.check A τ a ha).bind _ = _
  rw [h₁, Option.bind_some, hl, ite_eq_left rfl, h₂]

def productHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (.block [])
    (.seq (workspaceTaint true) (mulHint true) selectHint)

def bodyHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) productHint
    (.seq (workspaceTaint true) (mulHint true) (.block []))

def stepHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) bodyHint (.block [])

def counterEndTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .esi], flags := true }

theorem exponentProduct_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint true) (exponentProduct n) productHint = some (rowTaint true) := by
  unfold exponentProduct productHint
  exact exponent_check_seq taint (exponentMask_taint _ _) (by rfl)
    (exponent_check_seq taint (mul_check true _ _ _ _ _ _)
      (by rfl) (selectProduct_check (contextMod n) (slot n 6) (slot n 7) 4))

theorem exponentBody_check (n expWords : Nat) (he : 0 < expWords) :
    VG.Taint.check taint (workspaceTaint true) (exponentBody n expWords) bodyHint = some (zeroTaint true) := by
  unfold exponentBody bodyHint
  refine exponent_check_seq taint (exponentProduct_check n) (by rfl)
    (exponent_check_seq taint (mul_check true _ _ _ _ _ _) (by rfl) ?_)
  change taint.checkBlock (workspaceTaint true) (shiftExponent expWords (slot n 8)) = _
  rw [shiftExponent_taint, ite_eq_right (by omega)]
  rfl

theorem exponentStep_check (n expWords : Nat) (he : 0 < expWords) :
    VG.Taint.check taint (workspaceTaint true) (exponentStep n expWords) stepHint = some counterEndTaint := by
  unfold exponentStep stepHint
  exact exponent_check_seq taint (exponentBody_check n expWords he) (by rfl) (by rfl)

def exponentiateHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (mulHint false)
    (.seq (workspaceTaint false) (mulHint false)
      (.seq (workspaceTaint true) (.block [])
        (.seq (workspaceTaint false) (.loop (workspaceTaint true) stepHint) (mulHint false))))

theorem exponentiate_check (n expWords : Nat) (he : 0 < expWords) :
    VG.Taint.check taint (workspaceTaint false) (exponentiate n expWords) exponentiateHint = some (rowTaint false) := by
  have loop : VG.Taint.check taint (workspaceTaint true) (.loop (exponentStep n expWords) .ne)
      (.loop (workspaceTaint true) stepHint) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) (exponentStep n expWords) stepHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [exponentStep_check n expWords he]
    rfl
  unfold exponentiate exponentiateHint
  refine exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) ?_
  refine exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) ?_
  refine exponent_check_seq taint (u := workspaceTaint true) (by rfl) (by rfl) ?_
  exact exponent_check_seq taint loop (by rfl) (mul_check false _ _ _ _ _ _)

/-- Neither the modulus, base, exponent nor intermediate values need to be
public. Only the common workspace pointer is public on entry. -/
theorem exponentiate_constantTime (n expWords : Nat) (he : 0 < expWords) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (exponentiate n expWords) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := exponentiateHint) ?_
  rw [exponentiate_check n expWords he]
  rfl

end VG.Proof.Mont.X86.Dynamic
