module

public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Constant-time modular doubling and Montgomery setup -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def doubleHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (addHint true) (.block [])

def powerHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (oneHint false)
    (.seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) doubleHint))

theorem powerTwo_check (M : VG.Impl.Mont.Mod) (acc out bits : Nat) :
    VG.Taint.check taint (workspaceTaint false) (powerTwo M acc out bits) powerHint = some counterEndTaint := by
  have body : VG.Taint.check taint (workspaceTaint true) (doubleStep M acc out) doubleHint =
      some counterEndTaint :=
    exponent_check_seq taint (add_check true M acc out out out) (by rfl) (by rfl)
  unfold powerTwo powerHint
  refine exponent_check_seq taint (one_check false M.n out) (by rfl) ?_
  refine exponent_check_seq taint (u := workspaceTaint true) (by rfl) (by rfl) ?_
  change (if taint.le (workspaceTaint true) (workspaceTaint true) then
    (VG.Taint.check taint (workspaceTaint true) (doubleStep M acc out) doubleHint).bind
      (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
    else none) = _
  rw [body]
  rfl

def contextSetupHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (.block []) (.seq (workspaceTaint false) (oneHint false) powerHint)

theorem contextSetup_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (contextSetup n) contextSetupHint = some counterEndTaint :=
  exponent_check_seq taint (setupInverse_taint false (slot n 0) 0) (by rfl)
    (exponent_check_seq taint (one_check false n (slot n 3)) (by rfl)
      (powerTwo_check (contextMod n) (slot n 2) (slot n 4) (128 * n)))

end VG.Proof.Mont.X86.Dynamic
