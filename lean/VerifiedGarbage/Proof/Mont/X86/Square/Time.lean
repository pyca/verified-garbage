module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
meta import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import Init.Prelude
meta import Init.Prelude
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Rsa.MontMulContract
meta import VerifiedGarbage.Proof.Rsa.MontMulContract
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section
namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont.X86.Rt

theorem constantTime :
    ConstantTime isa (Proof.Rsa.MontMul.mulContract abi 0).pre (Proof.Rsa.MontMul.mulContract abi 0).pub Impl.Mont.X86.Rt.Square.dispatch :=
  VG.Taint.constantTime (A := sseTaint) rtTaint (fun _ _ h1 h2 hp =>
    rtTaint_agree (rtAbi_of h1) (rtAbi_of h2) (rt_publicArgs hp).1 (rt_publicArgs hp).2) (by taint_decide)

end VG.Proof.Mont.X86.Square
