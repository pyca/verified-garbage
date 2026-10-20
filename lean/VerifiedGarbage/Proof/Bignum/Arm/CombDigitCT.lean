module

public import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Gathering a digit addresses and branches only on public bit positions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm

/-- Exponent values remain secret; the five gather controls are public. -/
def Public (s t : State) : Prop :=
  ∀ r ∈ ([.r4,.r5,.r6,.r7,.r8] : List Reg), s.gpr r = t.gpr r

theorem code_ct : ConstantTime isa (fun _ => True) Public VG.Impl.Bignum.Arm.CombDigit.code := by
  apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r4,.r5,.r6,.r7,.r8])
  · intro s t _ _ h
    exact Taint.agree_ofRegs h
  · taint_decide

end VG.Proof.Bignum.Arm.CombDigit
