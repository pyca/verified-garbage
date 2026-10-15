module

public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming

/-! # Constant-time ordinary modular products and sums -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem ordinaryMul_constantTime (n : Nat) (hn : 0 < n) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (ordinaryMul n) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := .seq (workspaceTaint false) (mulHint false) (mulHint false)) ?_
  have chk : VG.Taint.check taint (workspaceTaint false) (ordinaryMul n)
      (.seq (workspaceTaint false) (mulHint false) (mulHint false)) = some (rowTaint false) :=
    exponent_check_seq taint (mul_check false _ _ _ _ _ _ (by change 0 < 2 * n; omega)) (by rfl)
      (mul_check false _ _ _ _ _ _ (by change 0 < 2 * n; omega))
  rw [chk]
  rfl

theorem ordinaryAdd_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint true)) (.block (ordinaryAdd n)) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint true) (fun _ _ _ _ h => h) (hc := .block []) ?_
  change (taint.checkBlock (workspaceTaint true) (ordinaryAdd n)).isSome = true
  rw [ordinaryAdd, add_counter_taint]
  rfl

end VG.Proof.Dsa.X86
