module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow

/-! # The taint check of CRT parameter calculation at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86

/-- The arguments, `edi` and `esp`. -/
def τV : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 68 }

theorem sizedCheck :
    (VG.Taint.check taint τV VG.Impl.Rsa.X86.CrtValuesRt.sized
      (VG.Taint.hintOf taint τV VG.Impl.Rsa.X86.CrtValuesRt.sized)).isSome = true := by
  taint_decide

end VG.Proof.Rsa.X86.CrtValuesRt
