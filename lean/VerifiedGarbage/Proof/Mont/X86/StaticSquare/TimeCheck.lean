module

public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Mont.X86.StaticSquare
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Constant-time checks for the fixed scalar square schedules -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont.X86.Rt

theorem square64_check : (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 64)
    (VG.Taint.hintOf taint rtTaint (Impl.Mont.X86.Rt.StaticSquare.square 64))).isSome=true := by
  taint_decide

theorem square96_check : (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 96)
    (VG.Taint.hintOf taint rtTaint (Impl.Mont.X86.Rt.StaticSquare.square 96))).isSome=true := by
  taint_decide

theorem square128_check : (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 128)
    (VG.Taint.hintOf taint rtTaint (Impl.Mont.X86.Rt.StaticSquare.square 128))).isSome=true := by
  taint_decide

end VG.Proof.Mont.X86.StaticSquare
