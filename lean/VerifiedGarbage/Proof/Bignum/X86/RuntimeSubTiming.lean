module
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The unrolled modular subtraction uses only fixed workspace addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem chainList_check (js : List Nat) (op op' : AluOp) (out a b : Nat) :
    taint.checkBlock (workspaceTaint false) (js.flatMap fun j =>
      [.mov .eax (.mem (sc (a + 4 * j))), .alu (if j = 0 then op else op') .eax (.mem (sc (b + 4 * j))),
        .store (sc (out + 4 * j)) .eax]) = some (workspaceTaint false) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.flatMap_cons, exponent_check_append taint (workspaceTaint false)]
    have step : taint.checkBlock (workspaceTaint false)
        [.mov .eax (.mem (sc (a + 4 * j))), .alu (if j = 0 then op else op') .eax (.mem (sc (b + 4 * j))),
          .store (sc (out + 4 * j)) .eax] = some (workspaceTaint false) := by
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
      change taint.checkBlock (workspaceTaint false)
        [.mov .eax (.mem (sc 0)), .alu (if j = 0 then op else op') .eax (.mem (sc 0)),
          .store (sc 0) .eax] = _
      by_cases h : j = 0
      · simp only [h, ite_true]; cases op <;> rfl
      · simp only [h, ite_false]; cases op' <;> rfl
    rw [step]
    exact ih

theorem maskedList_check (js : List Nat) (mo tmp : Nat) :
    taint.checkBlock (workspaceTaint false) (js.flatMap fun j =>
      [.mov .edx (.mem (sc (mo + 4 * j))), .alu .and .edx (.reg .eax),
        .store (sc (tmp + 4 * j)) .edx]) = some (workspaceTaint false) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.flatMap_cons, exponent_check_append taint (workspaceTaint false)]
    have step : taint.checkBlock (workspaceTaint false)
        [.mov .edx (.mem (sc (mo + 4 * j))), .alu .and .edx (.reg .eax),
          .store (sc (tmp + 4 * j)) .edx] = some (workspaceTaint false) := by
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
      change taint.checkBlock (workspaceTaint false)
        [.mov .edx (.mem (sc 0)), .alu .and .edx (.reg .eax), .store (sc 0) .edx] = _
      rfl
    rw [step]
    exact ih

theorem runtimeSub_check (M : Mod) (acc out a b : Nat) :
    taint.checkBlock (workspaceTaint false) (sub M acc out a b) = some (workspaceTaint false) := by
  unfold sub
  apply check_append_of taint (workspaceTaint false)
  · apply check_append_of taint (workspaceTaint false)
    · apply check_append_of taint (workspaceTaint false)
      · exact chainList_check _ _ _ _ _ _
      · rfl
    · exact maskedList_check _ _ _
  · exact chainList_check _ _ _ _ _ _

theorem runtimeSub_relCT (M : Mod) (acc out a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (sub M acc out a b))
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (runtimeSub_check M acc out a b) (by rfl)

end VG.Proof.Bignum.X86
