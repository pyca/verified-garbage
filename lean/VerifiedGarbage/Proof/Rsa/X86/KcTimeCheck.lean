module

public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The taint checks of the key checks at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86

/-- The bytes of the return address and the arguments. -/
def argSpan (full : Bool) : Nat := 4 * (VG.Impl.Rsa.X86.KeyCheck.scratchArg full + 3)

/-- The arguments, `edi` and `esp`. -/
def τV (full : Bool) : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := argSpan full }

end VG.Proof.Rsa.X86.KeyCheck
