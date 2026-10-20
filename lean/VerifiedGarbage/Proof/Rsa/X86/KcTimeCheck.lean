module

public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # The taint checks of the key checks at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86

/-- The bytes of the return address and the arguments. -/
def argSpan (full : Bool) : Nat := 4 * (VG.Impl.Rsa.X86.KeyCheck.scratchArg full + 3)

/-- The arguments, `edi` and `esp`. -/
def τV (full : Bool) : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := argSpan full }

theorem sizedCheckFull :
    (VG.Taint.check taint (τV true) (VG.Impl.Rsa.X86.KeyCheckRt.sized true)
      (VG.Taint.hintOf taint (τV true) (VG.Impl.Rsa.X86.KeyCheckRt.sized true))).isSome = true := by
  taint_decide

theorem sizedCheckCrt :
    (VG.Taint.check taint (τV false) (VG.Impl.Rsa.X86.KeyCheckRt.sized false)
      (VG.Taint.hintOf taint (τV false) (VG.Impl.Rsa.X86.KeyCheckRt.sized false))).isSome = true := by
  taint_decide

theorem sizedCheck (full : Bool) :
    (VG.Taint.check taint (τV full) (VG.Impl.Rsa.X86.KeyCheckRt.sized full)
      (VG.Taint.hintOf taint (τV full) (VG.Impl.Rsa.X86.KeyCheckRt.sized full))).isSome = true := by
  cases full
  · exact sizedCheckCrt
  · exact sizedCheckFull

end VG.Proof.Rsa.X86.KeyCheck
