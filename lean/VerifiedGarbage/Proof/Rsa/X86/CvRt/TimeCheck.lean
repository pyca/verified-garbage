module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # The taint check of CRT parameter calculation at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86

/-- The arguments, `edi` and `esp`. -/
def τV : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 68 }

def beforeInverse : Prog isa := .seq VG.Impl.Rsa.X86.CrtValuesRt.loads
  (.seq VG.Impl.Rsa.X86.CrtValuesRt.firstDiv (VG.Impl.Rsa.X86.Keys.seqs VG.Impl.Rsa.X86.CrtValuesRt.checksPrefix))
def afterInverse : Prog isa := .seq (VG.Impl.Rsa.X86.Keys.seqs VG.Impl.Rsa.X86.CrtValuesRt.checksSuffix)
  (.seq (VG.Impl.Rsa.X86.CrtValuesRt.div VG.Impl.Rsa.X86.CrtValues.aDR2)
    (.seq VG.Impl.Rsa.X86.CrtValuesRt.divQ VG.Impl.Rsa.X86.CrtValuesRt.stores))

theorem beforeCheck :
    (VG.Taint.check taint τV beforeInverse (VG.Taint.hintOf taint τV beforeInverse)).isSome=true := by
  taint_decide

theorem afterCheck :
    (VG.Taint.check taint τV afterInverse (VG.Taint.hintOf taint τV afterInverse)).isSome=true := by
  taint_decide

end VG.Proof.Rsa.X86.CrtValuesRt
